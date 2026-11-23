/-
  LeanVM.Guest.B1.Whir.CRoundsA

  The fold rounds, inline, as blocks at fixed values.
-/

module

public import LeanVM.Guest.B1.Whir.CAtoms
public import LeanVM.Guest.B1.Whir.CLow
public import LeanVM.Guest.B1.Whir.RoundComplete
public import LeanVM.Guest.B1.Bits.GrindWin

/-!
# The fold rounds at fixed values

`gc_blk`: an inline `grind_check` whose word passes, on memories holding the window table and
agreeing with `rd0` below `2^11` (`LowAgree`), at its honest values (`gcVals` on `rd0`); its loads
read the window table on every memory holding it (`gc_loadsHold`), its windows exact (`gcInline_exact_of_vals`).

`RoundH rd fch coefs tabs cur i fs xs`: what a round reads of the memory (its five words at
the cursor, `α` at `fch` slot `i`, `α, β` at `coefs` slots `2i, 2i + 1`, the window table);
`RoundsH`: `n` rounds' from `i`, their grinds passing. `osRound_completeA`, `osRounds_completeA`:
the inline rounds (`osRound`, its core `osRoundCore`) as blocks at fixed values on memories
agreeing with `rd0` below `2^11`, leaving the capacity and claim of `roundsTr`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

theorem ldT_rename (r : V → V) (s : Stmt) :
    ldT (s.rename r) = (ldT s).map (fun q ↦ (r q.1, r q.2.1, q.2.2)) := by
  cases s with
  | atom a => cases a <;> simp [Stmt.rename, Atom.rename, ldT]
  | _ => simp [Stmt.rename, ldT]

theorem renameList_ldT (r : V → V) : ∀ ss : List Stmt,
    (Stmt.renameList r ss).filterMap ldT = (ss.filterMap ldT).map (fun q ↦ (r q.1, r q.2.1, q.2.2))
  | [] => by simp [Stmt.renameList]
  | s :: ss => by
    rw [Stmt.renameList, List.filterMap_cons, List.filterMap_cons, ldT_rename, renameList_ldT r ss]
    cases ldT s <;> simp

theorem loadsHold_rename {rd : Reader} {σ : Val} (r : V → V) (ss : List Stmt) :
    LoadsHold rd σ (Stmt.renameList r ss) ↔ LoadsHold rd (σ ∘ r) ss := by
  unfold LoadsHold
  rw [renameList_ldT]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Function.comp]

theorem loadsHold_flatten {rd : Reader} {σ : Val} :
    ∀ L : List (List Stmt), LoadsHold rd σ L.flatten ↔ ∀ l ∈ L, LoadsHold rd σ l
  | [] => by simp [LoadsHold]
  | l :: L => by
    rw [List.flatten_cons, loadsHold_append, loadsHold_flatten L]
    simp

/-- **An inline `grind_check`'s loads** read the window table, at its honest values on any memory. -/
theorem gc_loadsHold {rd rd0 : Reader} {b o : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V} {σ : Val}
    (ht : WinTabs rd (σ tabs))
    (hσ : ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd0 b (σ w) (σ tabs) k) :
    LoadsHold rd σ (gcInlineT b o w tabs) := by
  obtain ⟨-, hT, hsum⟩ := gc_shape b hb
  have hτ : ∀ k, 2 ≤ k → k < gcLen b → (σ ∘ gcRen o w tabs) (.n k) = gcVals rd0 b (σ w) (σ tabs) k :=
    fun k h2 hk ↦ by rw [Function.comp, gcRen_own o w tabs h2]; exact hσ k h2 hk
  have hV0 : gcV b (σ w) 0 < 2 ^ 11 :=
    lt_of_lt_of_le (gcV_zero_lt hsum _) (Nat.pow_le_pow_right (by decide) hT)
  have e1 : (σ ∘ gcRen o w tabs) (.n 1) = σ tabs := rfl
  rw [gcInlineT, loadsHold_rename, gcPre, loadsHold_append, loadsHold_append, loadsHold_flatten]
  refine ⟨⟨?_, fun l hl ↦ ?_⟩, ?_⟩
  · have e : (gcHead b).filterMap ldT = [(.n (gcW b + 8), .n (gcW b + 7), 0)] := rfl
    intro q hq
    rw [e, List.mem_singleton] at hq
    subst hq
    show LoadHolds rd ((σ ∘ gcRen o w tabs) (.n (gcW b + 7))) 0 ((σ ∘ gcRen o w tabs) (.n (gcW b + 8)))
    have e7 : gcVals rd0 b (σ w) (σ tabs) (gcW b + 7) = σ tabs * gen ^ gcV b (σ w) 0 := gv_top_ptr
    have e8 : gcVals rd0 b (σ w) (σ tabs) (gcW b + 8) = eOfNat (gcV b (σ w) 0) := by
      rw [show gcW b + 8 = gcW b + 9 * 0 + 8 by ring]; exact gv_acc (i := 0) (by omega)
    rw [hτ _ (by omega) (by unfold gcLen; omega), hτ _ (by omega) (by unfold gcLen; omega), e7, e8]
    exact winTab_load ht hV0
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    have hi' := List.mem_range.mp hi
    have e : (gcIterAt (gcW b) (i + 1)).filterMap ldT =
        [(.n (gcW b + 9 * (i + 1) + 7), .n (gcW b + 9 * (i + 1) + 6), 0)] := rfl
    intro q hq
    rw [e, List.mem_singleton] at hq
    subst hq
    show LoadHolds rd ((σ ∘ gcRen o w tabs) (.n (gcW b + 9 * (i + 1) + 6))) 0
      ((σ ∘ gcRen o w tabs) (.n (gcW b + 9 * (i + 1) + 7)))
    rw [hτ _ (by omega) (by unfold gcLen; omega), hτ _ (by omega) (by unfold gcLen; omega),
      gv_iter (by omega) (by omega) (by omega), gv_iter (by omega) (by omega) (by omega)]
    exact winTab_load ht (Nat.mod_lt _ (by positivity))
  · have e : (gcTailPre b).filterMap ldT = [] := rfl
    intro q hq
    rw [e] at hq
    exact absurd hq List.not_mem_nil

/-- **An inline `grind_check`**, its word at `wi` passing, at its honest values on `rd0`, its loads
in the window table. -/
theorem gc_blk {σ : Val} {b o wi ti : ℕ} (rd0 : Reader) (hl0 : LowDef 11 rd0)
    (hb : b ∈ grindBitsDeployed) (hwo : wi < o) (hto : ti < o)
    (hlow : ((σ (.n wi)).limb 0).lane.toNat % 2 ^ b = 0)
    (hag0 : ∀ C rd, H C rd → LowAgree rd rd0) (htM : ∀ C rd, HM M H C rd → WinTabs rd (σ (.n ti))) :
    BlkA M H σ o (o + (gcLen b - 2)) (gcInlineT b o (.n wi) (.n ti)) (fun _ ↦ True) := by
  refine BlkA.mk (fun i ↦ gcVals rd0 b (σ (.n wi)) (σ (.n ti)) (i + 2 - o))
    (fun C rd hH' σ' ha hr ↦ ⟨?_, trivial⟩) (fun C rd hH' σ' ha hr rd' hm ↦ ?_) fun σ' ha hr ↦ ?_
  · have ht := htM C rd (.inl hH')
    have hag := hag0 C rd hH'
    have ew : σ' (.n wi) = σ (.n wi) := ha _ hwo
    have et : σ' (.n ti) = σ (.n ti) := ha _ hto
    have hh := gcInline_complete_of (C := C) (rd := rd) (gcRc_of_lowDef (le_refl 11) (hag.lowDef hl0)) hb
      (o := o) (w := .n wi) (tabs := .n ti) (σ := σ') (by rw [et]; exact ht) (by rw [ew]; exact hlow)
      (fun k hk2 hk ↦ by
        rw [hr _ (by omega) (by omega), ew, et, gcVals_agree hag hb]
        dsimp only
        rw [show o + k - 2 + 2 - o = k by omega])
      trivial (kret := fun _ ↦ True)
    exact ((holdsList_flat _ (gcInlineT_flat b o _ _) True (fun _ ↦ True)).mp hh).1
  · have ew : σ' (.n wi) = σ (.n wi) := ha _ hwo
    have et : σ' (.n ti) = σ (.n ti) := ha _ hto
    exact gc_loadsHold (rd0 := rd0) hb (by rw [et]; exact htM _ rd' (.inr ⟨hm, rfl, C, rd, hH'⟩))
      fun k hk2 hk ↦ by
        rw [hr _ (by omega) (by omega), ew, et]
        dsimp only
        rw [show o + k - 2 + 2 - o = k by omega]
  · have ew : σ' (.n wi) = σ (.n wi) := ha _ hwo
    have et : σ' (.n ti) = σ (.n ti) := ha _ hto
    intro s hs
    obtain ⟨a, rfl, hx⟩ := gcInline_exact_of_vals (rd0 := rd0) (σ := σ') hb (fun k hk2 hk ↦ by
      rw [hr _ (by omega) (by omega), ew, et]
      dsimp only
      rw [show o + k - 2 + 2 - o = k by omega]) s hs
    exact fun _ ↦ hx

/-- A grind passing gives its word's low bits. -/
theorem grindOk_low {s : Fs} {bits : ℕ} {n : E} (hb : bits ≠ 0) (h : s.GrindOk bits n) :
    ((cellsOfState (s.nonceState n) false 1).limb 0).lane.toNat % 2 ^ bits = 0 := by
  rcases h with h | h
  · exact absurd h hb
  · rw [Keccak.powLane_cells] at h
    exact of_decide_eq_true h

/-- **What a round reads of the memory.** -/
def RoundH (rd : Reader) (fch coefs tabs cur : E) (i : ℕ) (fs xs : List E) : Prop :=
  ReadsAt rd cur xs ∧ WinTabs rd tabs ∧ LoadHolds rd fch i (roundChs fs xs).1 ∧
    LoadHolds rd coefs (2 * i) (roundChs fs xs).2.1 ∧ LoadHolds rd coefs (2 * i + 1) (roundChs fs xs).2.2

/-- **What `n` rounds from `i` read of the memory**, their grinds passing. -/
def RoundsH (rd : Reader) (fch coefs tabs : E) : ℕ → ℕ → List E → E → E → List E → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, i, fs, cl, cur, xs =>
    RoundGrinds fs (xs.take 5) ∧ RoundH rd fch coefs tabs cur i fs (xs.take 5) ∧
      RoundsH rd fch coefs tabs n (i + 1) ((roundRets fs 0 cl (xs.take 5)).take 5)
        ((roundRets fs 0 cl (xs.take 5)).getD 6 0) (cur * gen ^ 5) (xs.drop 5)

/-- What a round leaves. -/
structure RoundOutA (σ σ' : Val) (st st' : OsSt) (xs : List E) : Prop where
  F : st'.F σ' = ⟨(roundRets (st.fsv σ) 0 (σ (.n st.claim)) xs).take 5, []⟩
  claim : σ' (.n st'.claim) = (roundRets (st.fsv σ) 0 (σ (.n st.claim)) xs).getD 6 0
  ok : st'.Ok σ'
  cur : st'.cur σ' = st.cur σ * gen ^ 5
  co : st'.co = st.co + 5
  pad : st'.pad = st.pad
  k : st.k ≤ st'.k

theorem osRound_k (cp last : Bool) (i : ℕ) (st : OsSt) (hk : 5 ≤ st.k) :
    st.k ≤ (osRound cp last i st).2.k := by
  unfold osRound osRoundD osRoundC; dsimp only
  cases cp <;> cases last <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem osRound_state (cp last : Bool) (i : ℕ) (st : OsSt) :
    (osRound cp last i st).2.cb = st.cb ∧ (osRound cp last i st).2.co = st.co + 5 ∧
      (osRound cp last i st).2.pad = st.pad ∧ (osRound cp last i st).2.mats = st.mats ∧
      (osRound cp last i st).2.fs.length = 5 := by
  unfold osRound; dsimp only; cases last <;> simp

/-- **One round, inline, as a block at fixed values.** -/
theorem osRound_completeA (rd0 : Reader) (hl0 : LowDef 11 rd0) {cp last : Bool} {i : ℕ} {st : OsSt}
    (σ : Val) (xs : List E) (hxl : xs.length = 5) (hsf : st.Sf) (hco : st.co + 5 < u128Bound)
    (hpad : ∃ p, st.pad = some p) (hok : ∀ C rd, HM M H C rd → st.Ok σ)
    (hg : RoundGrinds (st.fsv σ) xs)
    (hH : ∀ C rd, HM M H C rd → RoundH rd (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) (st.cur σ) i
      (st.fsv σ) xs) (hag0 : ∀ C rd, H C rd → LowAgree rd rd0) :
    BlkA M H σ st.k (osRound cp last i st).2.k (osRound cp last i st).1
      (fun σ' ↦ RoundOutA σ σ' st (osRound cp last i st).2 xs ∧ AgreeBelow st.k σ σ') := by
  refine BlkA.of_ne fun ⟨C0, rd1, hH1⟩ ↦ ?_
  obtain ⟨p, hp⟩ := hpad
  have hpd : st.pad.getD osPadV = p := by rw [hp]; rfl
  have hpb : p + 4 < st.k := hsf.padB p hp
  have hz := (hok C0 rd1 hH1).pad p hp
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have k33 : 43 ≤ st.k := hsf.k
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hsf.fs
  have hfb : ∀ f ∈ st.fs, f < st.k := hsf.below.fs
  rw [hf] at hfb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hfb
  obtain ⟨b0, b1, b2, b3, b4⟩ := hfb
  obtain ⟨u0, w, c0, c1, n2, rfl⟩ : ∃ u0 w c0 c1 n2, xs = [u0, w, c0, c1, n2] := by
    match xs, hxl with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  set fsv := st.fsv σ with hfsv
  have hfv : fsv = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [hfsv, OsSt.fsv, hf]
  set k := st.k with hk
  set b := if cp then k else k - 5 with hb
  set cap := if cp then (List.range 5).map (k + ·) else st.fs with hcap
  set S1 := rdS1 fsv [u0, w, c0, c1, n2] with hS1
  set S3 := rdS3 fsv [u0, w, c0, c1, n2] with hS3
  set S4 := rdS4 fsv [u0, w, c0, c1, n2] with hS4
  set cl := σ (.n st.claim) with hcl
  have hspg := rd_sponges (σ (.n f0)) (σ (.n f1)) (σ (.n f2)) (σ (.n f3)) (σ (.n f4)) 0 0 0 0 0 u0 w c0 c1 n2
  simp only at hspg
  rw [← hfv] at hspg
  have e3 : rdS3 [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4), 0, 0, 0, 0, 0]
      [u0, w, c0, c1, n2] = S3 := by rw [hS3, hfv]; rfl
  have e4 : rdS4 [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4), 0, 0, 0, 0, 0]
      [u0, w, c0, c1, n2] = S4 := by rw [hS4, hfv]; rfl
  rw [e3, e4] at hspg
  obtain ⟨hN, hG2, hSq⟩ := hspg
  set C := osRoundC b with hC
  set D := osRoundD b with hD
  have hgl : 3 ≤ gcLen foldGrind := by unfold gcLen; omega
  have hCb : C = b + 46 + (gcLen foldGrind - 2) := by rw [hC, osRoundC]; omega
  have hDC : D = C + 13 := rfl
  have kb : b + 5 = if cp then k + 5 else k := by rw [hb]; split_ifs <;> omega
  have hbk : k ≤ b + 5 := by rw [kb]; split_ifs <;> omega
  have hbk' : b ≤ k := by rw [hb]; split_ifs <;> omega
  -- the capacity cells
  have B0 : BlkA M H σ k (b + 5) (if cp then (List.range 5).map (fun i ↦ osCp (k + i) (st.fs.getD i 0)) else [])
      (fun σ' ↦ cap.map (fun j ↦ σ' (.n j)) = fsv) := by
    cases cp
    · simp only [Bool.false_eq_true, ↓reduceIte] at kb ⊢
      rw [kb]
      refine BlkA.nil fun σ' ha ↦ ?_
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, hf, hfv, List.map_cons, List.map_nil,
        ha _ b0, ha _ b1, ha _ b2, ha _ b3, ha _ b4]
    · simp only [↓reduceIte] at kb ⊢
      rw [kb]
      refine blk_lst fsv (by simp [hfv]) fun C rd _ σ' ha hv ↦ ?_
      have v : ∀ j < 5, σ' (.n (k + j)) = fsv.getD j 0 := fun j hj ↦ hv j (by simp [hfv]; omega)
      rw [hfv] at v
      have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
      have v3 := v 3 (by omega); have v4 := v 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
      refine ⟨?_, ?_⟩
      · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
          List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, osCp, hf,
          List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
        rw [v0, v1, v2, v3, v4, ha _ b0, ha _ b1, ha _ b2, ha _ b3, ha _ b4]
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp only [hcap, ↓reduceIte, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
          List.nil_append, List.cons_append, Nat.add_zero, hfv]
        rw [v0, v1, v2, v3, v4]
  -- the four scalars
  have hcur : ∀ C rd, HM M H C rd → ∀ t < 5, LoadHolds rd (σ (.n st.cb)) (st.co + t) ([u0, w, c0, c1, n2].getD t 0) :=
    fun C rd hC' t ht ↦ by
      have := (hH C rd hC').1 t (by simpa using ht)
      rw [OsSt.cur, loadHolds_mul_gen_pow] at this
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      exact this
  have hcb : st.cb < k := hsf.below.cb
  have hclk : st.claim < k := hsf.below.claim
  have hcapv : ∀ j ∈ cap, j < b + 5 := by
    intro j hj
    by_cases hc : cp = true
    · simp only [hcap, hc, ↓reduceIte, List.mem_map, List.mem_range] at hj
      simp only [hc, ↓reduceIte] at hb
      obtain ⟨a, ha, rfl⟩ := hj; omega
    · simp only [hcap, hc, Bool.false_eq_true, ↓reduceIte, hf, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  have hcapl : cap.length = 5 := by cases cp <;> simp [hcap, hf]
  set L1 : List E := [u0, u0, word 0 1, w, w, word 0 1, c0, c0, word 0 1, c1, c1, word 0 1] with hL1
  have A1 := BlkA.seq (M := M) (H := H) hbk (show b + 5 ≤ b + 17 by omega) B0
    (B := ((List.range 4).map fun t ↦ [osLd (b + 5 + 3 * t) st.cb (st.co + t),
      osCp (b + 6 + 3 * t) (b + 5 + 3 * t), osCst (b + 7 + 3 * t) (word 0 1)]).flatten)
    (OutB := fun σ' ↦ ∀ j < 12, σ' (.n (b + 5 + j)) = L1.getD j 0) fun σ1 ha1 _ ↦
    blk_lst L1 (by simp [hL1]) fun C rd hH σ' ha hv ↦ by
      have v : ∀ j < 12, σ' (.n (b + 5 + j)) = L1.getD j 0 := fun j hj ↦ hv j (by simp [hL1]; omega)
      refine ⟨?_, v⟩
      have ecb : σ' (.n st.cb) = σ (.n st.cb) := by rw [ha _ (by omega), ha1 _ hcb]
      have lc := hcur C rd hH
      simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.flatten_cons, List.flatten_nil, List.append_nil, allOk_cons, allOk_nil,
        and_true, stmtOk_atom, holds_load, holds_copy, holds_const, osLd, osCp, osCst, ecb]
      have w0 := v 0 (by omega); have w1 := v 1 (by omega); have w2 := v 2 (by omega)
      have w3 := v 3 (by omega); have w4 := v 4 (by omega); have w5 := v 5 (by omega)
      have w6 := v 6 (by omega); have w7 := v 7 (by omega); have w8 := v 8 (by omega)
      have w9 := v 9 (by omega); have w10 := v 10 (by omega); have w11 := v 11 (by omega)
      simp only [hL1, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
        show b + 5 + 1 = b + 6 by omega, show b + 5 + 2 = b + 7 by omega,
        show b + 5 + 3 = b + 5 + 3 * 1 by omega, show b + 5 + 4 = b + 6 + 3 * 1 by omega,
        show b + 5 + 5 = b + 7 + 3 * 1 by omega, show b + 5 + 6 = b + 5 + 3 * 2 by omega,
        show b + 5 + 7 = b + 6 + 3 * 2 by omega, show b + 5 + 8 = b + 7 + 3 * 2 by omega,
        show b + 5 + 9 = b + 5 + 3 * 3 by omega, show b + 5 + 10 = b + 6 + 3 * 3 by omega,
        show b + 5 + 11 = b + 7 + 3 * 3 by omega] at w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Nat.mul_zero, Nat.add_zero, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]
      · simpa using lc 0 (by omega)
      · simpa using lc 1 (by omega)
      · simpa using lc 2 (by omega)
      · simpa using lc 3 (by omega)
  -- the four scalars' permutation
  have eS1 : (⟨fsv, [(u0, dsObserve), (w, dsObserve), (c0, dsObserve), (c1, dsObserve)]⟩ : Fs).perm = S1 := by
    rw [hS1]; unfold rdS1; rw [hfv]; rfl
  have A2 := BlkA.seq (M := M) (H := H) (show k ≤ b + 17 by omega) (show b + 17 ≤ b + 17 + 13 by omega) A1
    (B := [osKeccak ([b + 6, b + 7, b + 9, b + 10, b + 12, b + 13, b + 15, b + 16] ++ cap) (b + 17)])
    (OutB := fun σ' ↦ ∀ j < 13, σ' (.n (b + 17 + j)) = rdCell S1 j) fun σ2 _ ho2 ↦ by
      obtain ⟨hc0, hv1⟩ := ho2 C0 rd1 hH1
      have g : ∀ j < 12, ∀ m, m = b + 5 + j → σ2 (.n m) = L1.getD j 0 := fun j hj m hm ↦ hm ▸ hv1 j hj
      refine (keccak_blk (M := M) (H := H) (σ := σ2) (out := b + 17)
        (⟨fsv, [(u0, dsObserve), (w, dsObserve), (c0, dsObserve), (c1, dsObserve)]⟩ : Fs) (by simp)
        (by simp [hcapl]) (fun i hi ↦ ?_) (fun C rd _ ↦ ?_)).mono fun σ' h j hj ↦ by rw [h j hj, eS1]
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hi
        all_goals first | omega | (have := hcapv i hi; omega)
      · rw [List.map_append, hc0]
        have e1 := g 1 (by omega) (b + 6) (by omega); have e2 := g 2 (by omega) (b + 7) (by omega)
        have e4 := g 4 (by omega) (b + 9) (by omega); have e5 := g 5 (by omega) (b + 10) (by omega)
        have e7 := g 7 (by omega) (b + 12) (by omega); have e8 := g 8 (by omega) (b + 13) (by omega)
        have e10 := g 10 (by omega) (b + 15) (by omega); have e11 := g 11 (by omega) (b + 16) (by omega)
        simp only [hL1, List.getD_cons_zero, List.getD_cons_succ] at e1 e2 e4 e5 e7 e8 e10 e11
        simp only [List.map_cons, List.map_nil, e1, e2, e4, e5, e7, e8, e10, e11]
        simp [pendCells, scalarCells_eq, word_dsObserve]
  -- the nonce
  set L3 : List E := [n2, n2, word 0 4] with hL3
  have A3 := BlkA.seq (M := M) (H := H) (show k ≤ b + 17 + 13 by omega) (show b + 30 ≤ b + 33 by omega)
    (by simpa only [show b + 17 + 13 = b + 30 by omega] using A2)
    (B := [osLd (b + 30) st.cb (st.co + 4), osCp (b + 31) (b + 30), osCst (b + 32) (word 0 4)])
    (OutB := fun σ' ↦ ∀ j < 3, σ' (.n (b + 30 + j)) = L3.getD j 0) fun σ3 ha3 _ ↦
    blk_lst L3 (by simp [hL3]) fun C rd hH σ' ha hv ↦ by
      have v : ∀ j < 3, σ' (.n (b + 30 + j)) = L3.getD j 0 := fun j hj ↦ hv j (by simp [hL3]; omega)
      refine ⟨?_, v⟩
      have ecb : σ' (.n st.cb) = σ (.n st.cb) := by rw [ha _ (by omega), ha3 _ hcb]
      have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
      simp only [hL3, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
        show b + 30 + 1 = b + 31 by omega, show b + 30 + 2 = b + 32 by omega] at v0 v1 v2
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_copy, holds_const,
        osLd, osCp, osCst, ecb, v0, v1, v2]
      simpa using hcur C rd hH 4 (by omega)
  -- the nonce's permutation
  have A4 := BlkA.seq (M := M) (H := H) (show k ≤ b + 33 by omega) (show b + 33 ≤ b + 33 + 13 by omega) A3
    (B := [osKeccak [b + 31, b + 32, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4, b + 17 + 8, b + 17 + 9,
      b + 17 + 10, b + 17 + 11, b + 17 + 12] (b + 33)])
    (OutB := fun σ' ↦ ∀ j < 13, σ' (.n (b + 33 + j)) = rdCell S3 j) fun σ4 ha4 ho4 ↦ by
      obtain ⟨⟨_, hv2⟩, hv3⟩ := ho4 C0 rd1 hH1
      have g : ∀ j < 3, ∀ m, m = b + 30 + j → σ4 (.n m) = L3.getD j 0 := fun j hj m hm ↦ hm ▸ hv3 j hj
      refine (keccak_blk (M := M) (H := H) (σ := σ4) (out := b + 33)
        (⟨capOf S1, [(n2, dsPowNonce)]⟩ : Fs) (by simp) (by simp) (fun i hi ↦ ?_)
        (fun C rd _ ↦ ?_)).mono fun σ' h j hj ↦ by rw [h j hj]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have e1 := g 1 (by omega) (b + 31) (by omega); have e2 := g 2 (by omega) (b + 32) (by omega)
        simp only [hL3, List.getD_cons_zero, List.getD_cons_succ] at e1 e2
        simp only [List.map_cons, List.map_nil, e1, e2, ha4 _ (show p + 1 < k by omega),
          ha4 _ (show p + 2 < k by omega), ha4 _ (show p + 3 < k by omega),
          ha4 _ (show p + 4 < k by omega), z1, z2, z3, z4, hv2 8 (by omega), hv2 9 (by omega),
          hv2 10 (by omega), hv2 11 (by omega), hv2 12 (by omega)]
        simp [pendCells, scalarCells_eq, capOf, ← rdCell_eq, dsPowNonce]
  -- the grind
  have hlow : ((rdCell S3 1).limb 0).lane.toNat % 2 ^ foldGrind = 0 := by
    have hg' : (rdS2 fsv [u0, w, c0, c1]).GrindOk foldGrind n2 := by
      simpa [RoundGrinds, show _root_.LeanVM.Parameters.Whir.foldGrindingBits = foldGrind from rfl] using hg
    have := grindOk_low (by decide) hg'
    rw [hN] at this
    rwa [show rdCell S3 1 = cellsOfState S3 false 1 from rdCell_eq S3 1]
  have A5 := BlkA.seq (M := M) (H := H) (show k ≤ b + 46 by omega) (show b + 46 ≤ b + 46 + (gcLen foldGrind - 2) by omega)
    (by simpa only [show b + 33 + 13 = b + 46 by omega] using A4)
    (B := gcInlineT foldGrind (b + 46) (.n (b + 33 + 1)) (.n osTabs)) (OutB := fun _ ↦ True)
    fun σ5 ha5 ho5 ↦ by
      have e1 : σ5 (.n (b + 33 + 1)) = rdCell S3 1 := (ho5 C0 rd1 hH1).2 1 (by omega)
      refine gc_blk (b := foldGrind) (o := b + 46) (wi := b + 33 + 1) (ti := osTabs) rd0 hl0 (by decide)
        (by omega) (by simp only [osTabs]; omega) (by rw [e1]; exact hlow)
        hag0 fun C rd hC' ↦ by
        rw [ha5 _ (by simp only [osTabs]; omega)]
        exact (hH C rd hC').2.1
  rw [← hCb] at A5
  -- `β`'s permutation
  have A6 := BlkA.seq (M := M) (H := H) (show k ≤ C by omega) (show C ≤ C + 13 by omega) A5
    (B := [osKeccak [p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4, b + 33 + 8, b + 33 + 9,
      b + 33 + 10, b + 33 + 11, b + 33 + 12] C])
    (OutB := fun σ' ↦ ∀ j < 13, σ' (.n (C + j)) = rdCell S4 j) fun σ6 ha6 ho6 ↦ by
      obtain ⟨⟨_, hv4⟩, -⟩ := ho6 C0 rd1 hH1
      refine (keccak_blk (M := M) (H := H) (σ := σ6) (out := C) (⟨capOf S3, []⟩ : Fs) (by simp) (by simp)
        (fun i hi ↦ ?_) (fun C rd _ ↦ ?_)).mono fun σ' h j hj ↦ by rw [h j hj]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · simp only [List.map_cons, List.map_nil, ha6 _ (show p + 1 < k by omega),
          ha6 _ (show p + 2 < k by omega), ha6 _ (show p + 3 < k by omega),
          ha6 _ (show p + 4 < k by omega), z1, z2, z3, z4, hv4 8 (by omega), hv4 9 (by omega),
          hv4 10 (by omega), hv4 11 (by omega), hv4 12 (by omega)]
        simp [pendCells, capOf, ← rdCell_eq]
  -- `α` and `β` stored
  have hch : roundChs fsv [u0, w, c0, c1, n2] = (rdCell S3 0, rdCell S3 0, rdCell S4 0) := by
    simp only [roundChs, List.getD_cons_zero, List.getD_cons_succ]
    rw [hSq, hG2]
    simp [Keccak.challengeOf_cells, ← rdCell_eq]
  have A7 := BlkA.seq (M := M) (H := H) (show k ≤ C + 13 by omega) (show C + 13 ≤ C + 13 by omega) A6
    (B := [osLd (b + 33) osFch i, osLd (b + 33) osCoefs (2 * i), osLd C osCoefs (2 * i + 1)])
    (OutB := fun _ ↦ True) fun σ7 ha7 ho7 ↦ stores_blk fun C' rd hC' σ' ha ↦ by
      obtain ⟨⟨⟨_, hv4⟩, -⟩, hv6⟩ := ho7 C0 rd1 hH1
      obtain ⟨-, -, l1, l2, l3⟩ := hH C' rd hC'
      rw [hch] at l1 l2 l3
      have eB : σ' (.n (b + 33)) = rdCell S3 0 := by rw [ha _ (by omega)]; simpa using hv4 0 (by omega)
      have eC : σ' (.n C) = rdCell S4 0 := by rw [ha _ (by omega)]; simpa using hv6 0 (by omega)
      have ef : σ' (.n osFch) = σ (.n osFch) := by
        rw [ha _ (by simp only [osFch]; omega), ha7 _ (by simp only [osFch]; omega)]
      have ec : σ' (.n osCoefs) = σ (.n osCoefs) := by
        rw [ha _ (by simp only [osCoefs]; omega), ha7 _ (by simp only [osCoefs]; omega)]
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd, eB, eC, ef, ec]
      exact ⟨l1, l2, l3⟩
  -- the folded claim
  set al := rdCell S3 0 with hal
  set be := rdCell S4 0 with hbe
  set L8 : List E := [be * c0, u0 + be * c0, u0 + cl, al * w, u0 + cl + al * w, c0 + c1,
    be * (c0 + c1), u0 + cl + al * w + be * (c0 + c1), al * (u0 + cl + al * w + be * (c0 + c1)),
    u0 + be * c0 + al * (u0 + cl + al * w + be * (c0 + c1))] with hL8
  have A8 := BlkA.seq (M := M) (H := H) (show k ≤ C + 13 by omega) (show C + 13 ≤ C + 13 + 10 by omega) A7
    (B := [osMul D C (b + 11), osAdd (D + 1) (b + 5) D, osAdd (D + 2) (b + 5) st.claim,
      osMul (D + 3) (b + 33) (b + 8), osAdd (D + 4) (D + 2) (D + 3), osAdd (D + 5) (b + 11) (b + 14),
      osMul (D + 6) C (D + 5), osAdd (D + 7) (D + 4) (D + 6), osMul (D + 8) (b + 33) (D + 7),
      osAdd (D + 9) (D + 1) (D + 8)])
    (OutB := fun σ' ↦ ∀ j < 10, σ' (.n (C + 13 + j)) = L8.getD j 0) fun σ8 ha8 ho8 ↦
    blk_lst L8 (by simp [hL8]) fun C' rd hC' σ' ha hv ↦ by
      have v : ∀ j < 10, σ' (.n (C + 13 + j)) = L8.getD j 0 := fun j hj ↦ hv j (by simp [hL8]; omega)
      refine ⟨?_, v⟩
      obtain ⟨⟨⟨⟨⟨⟨⟨_, hv1⟩, _⟩, _⟩, hv4⟩, -⟩, hv6⟩, -⟩ := ho8 C0 rd1 hH1
      have g1 : ∀ j < 12, ∀ m, m = b + 5 + j → σ' (.n m) = L1.getD j 0 := fun j hj m hm ↦ by
        rw [ha _ (by omega), hm]; exact hv1 j hj
      have x0 := g1 0 (by omega) (b + 5) (by omega); have x1 := g1 3 (by omega) (b + 8) (by omega)
      have x2 := g1 6 (by omega) (b + 11) (by omega); have x3 := g1 9 (by omega) (b + 14) (by omega)
      simp only [hL1, List.getD_cons_zero, List.getD_cons_succ] at x0 x1 x2 x3
      have eB : σ' (.n (b + 33)) = al := by rw [ha _ (by omega)]; simpa using hv4 0 (by omega)
      have eC : σ' (.n C) = be := by rw [ha _ (by omega)]; simpa using hv6 0 (by omega)
      have ecl : σ' (.n st.claim) = cl := by rw [ha _ (by omega), ha8 _ hclk]
      have d0 := v 0 (by omega); have d1 := v 1 (by omega); have d2 := v 2 (by omega)
      have d3 := v 3 (by omega); have d4 := v 4 (by omega); have d5 := v 5 (by omega)
      have d6 := v 6 (by omega); have d7 := v 7 (by omega); have d8 := v 8 (by omega)
      have d9 := v 9 (by omega)
      simp only [hL8, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, holds_add, osMul, osAdd,
        hDC, x0, x1, x2, x3, eB, eC, ecl, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9]
  -- the capacity after `β`, copied but after the last round
  have A9 := BlkA.seq (M := M) (H := H) (show k ≤ C + 13 + 10 by omega)
    (show C + 13 + 10 ≤ (if last then D + 10 else D + 15) by split_ifs <;> omega) A8
    (B := if last then [] else (List.range 5).map (fun j ↦ osCp (D + 10 + j) (C + 8 + j)))
    (OutB := fun σ' ↦ ∀ j < 5, σ' (.n (if last then C + 8 + j else D + 10 + j)) = rdCell S4 (8 + j))
    fun σ9 ha9 ho9 ↦ by
      obtain ⟨⟨⟨_, hv6⟩, -⟩, -⟩ := ho9 C0 rd1 hH1
      cases last
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine blk_lst ((List.range 5).map fun j ↦ rdCell S4 (8 + j)) (by simp; omega)
          fun C' rd _ σ' ha hv ↦ ?_
        have v : ∀ j < 5, σ' (.n (D + 10 + j)) = rdCell S4 (8 + j) := fun j hj ↦ by
          have := hv j (by simpa using hj)
          rw [List.getD_eq_getElem _ _ (by simpa using hj)] at this
          simpa [hDC] using this
        have u : ∀ j < 5, σ' (.n (C + 8 + j)) = rdCell S4 (8 + j) := fun j hj ↦ by
          rw [ha _ (by omega), show C + 8 + j = C + (8 + j) by omega]; exact hv6 _ (by omega)
        refine ⟨?_, v⟩
        simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
          List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, osCp]
        rw [v 0 (by omega), v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega),
          u 0 (by omega), u 1 (by omega), u 2 (by omega), u 3 (by omega), u 4 (by omega)]
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp only [↓reduceIte]
        refine BlkA.nil fun σ' ha j hj ↦ ?_
        rw [ha _ (by omega), show C + 8 + j = C + (8 + j) by omega]; exact hv6 _ (by omega)
  have hk' : (osRound cp last i st).2.k = if last then D + 10 else D + 15 := by
    unfold osRound; cases last <;> rfl
  have hfs' : (osRound cp last i st).2.fs = (List.range 5).map (fun j ↦ (if last then C + 8 + j else D + 10 + j)) := by
    unfold osRound; cases last <;> rfl
  have hcl' : (osRound cp last i st).2.claim = D + 9 := by unfold osRound; cases last <;> rfl
  have hcb' : (osRound cp last i st).2.cb = st.cb := by unfold osRound; cases last <;> rfl
  have hco' : (osRound cp last i st).2.co = st.co + 5 := by unfold osRound; cases last <;> rfl
  have hmats' : (osRound cp last i st).2.mats = st.mats := by unfold osRound; cases last <;> rfl
  have hpad' : (osRound cp last i st).2.pad = st.pad := by unfold osRound; cases last <;> rfl
  have hstm : (osRound cp last i st).1 =
      (if cp then (List.range 5).map (fun i ↦ osCp (k + i) (st.fs.getD i 0)) else []) ++
        ((List.range 4).map fun t ↦ [osLd (b + 5 + 3 * t) st.cb (st.co + t),
          osCp (b + 6 + 3 * t) (b + 5 + 3 * t), osCst (b + 7 + 3 * t) (word 0 1)]).flatten ++
        [osKeccak ([b + 6, b + 7, b + 9, b + 10, b + 12, b + 13, b + 15, b + 16] ++ cap) (b + 17)] ++
        [osLd (b + 30) st.cb (st.co + 4), osCp (b + 31) (b + 30), osCst (b + 32) (word 0 4)] ++
        [osKeccak [b + 31, b + 32, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4, b + 17 + 8, b + 17 + 9,
          b + 17 + 10, b + 17 + 11, b + 17 + 12] (b + 33)] ++
        gcInlineT foldGrind (b + 46) (.n (b + 33 + 1)) (.n osTabs) ++
        [osKeccak [p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4, b + 33 + 8, b + 33 + 9,
          b + 33 + 10, b + 33 + 11, b + 33 + 12] C] ++
        [osLd (b + 33) osFch i, osLd (b + 33) osCoefs (2 * i), osLd C osCoefs (2 * i + 1)] ++
        [osMul D C (b + 11), osAdd (D + 1) (b + 5) D, osAdd (D + 2) (b + 5) st.claim,
          osMul (D + 3) (b + 33) (b + 8), osAdd (D + 4) (D + 2) (D + 3), osAdd (D + 5) (b + 11) (b + 14),
          osMul (D + 6) C (D + 5), osAdd (D + 7) (D + 4) (D + 6), osMul (D + 8) (b + 33) (D + 7),
          osAdd (D + 9) (D + 1) (D + 8)] ++
        (if last then [] else (List.range 5).map (fun j ↦ osCp (D + 10 + j) (C + 8 + j))) := by
    show (if cp then _ else []) ++ osRoundCore b (st.pad.getD osPadV) st.cb st.co st.claim i cap ++
      (if last then [] else _) = _
    rw [hpd]
    unfold osRoundCore
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  have hrr : roundRets fsv 0 cl [u0, w, c0, c1, n2] =
      capOf S4 ++ [0 * gen ^ 5, roundClaim cl al be u0 w c0 c1] := by
    simp only [roundRets, List.getD_cons_zero, List.getD_cons_succ]
    rw [hSq, hG2]
    simp [Keccak.challengeOf_cells, ← rdCell_eq, hal, hbe]
  rw [hk', hstm]
  refine BlkA.monoH A9.agree fun C' rd hC' σ' _ ⟨ho, hag⟩ ↦ ?_
  obtain ⟨⟨_, hv8⟩, hv9⟩ := ho
  have hok' := (hok C' rd hC').agree hag
  have hkk : k ≤ (if last then D + 10 else D + 15) := by split_ifs <;> omega
  have e9 : σ' (.n (D + 9)) = roundClaim cl al be u0 w c0 c1 := by
    have := hv8 9 (by omega)
    simp only [hL8, List.getD_cons_zero, List.getD_cons_succ] at this
    rw [hDC, this]; rfl
  refine ⟨⟨?_, ?_, ⟨⟨?_, ⟨fun f hf ↦ ?_, ?_, ?_, fun m hm ↦ ?_⟩, ?_, fun q hq ↦ ?_, ?_⟩, ?_, ?_⟩, ?_,
    hco', hpad', by rw [hk']; exact hkk⟩, hag⟩
  · rw [OsSt.F, hfs', hrr]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append]
    rw [hv9 0 (by omega), hv9 1 (by omega), hv9 2 (by omega), hv9 3 (by omega), hv9 4 (by omega)]
    simp [capOf, ← rdCell_eq]
  · rw [hcl', hrr, e9]; simp [capOf]
  · rw [hfs']; simp
  · rw [hfs'] at hf
    rw [hk']
    simp only [List.mem_map, List.mem_range] at hf
    obtain ⟨j, hj, rfl⟩ := hf
    split_ifs <;> omega
  · rw [hcb', hk']; omega
  · rw [hcl', hk']; split_ifs <;> omega
  · rw [hmats'] at hm
    rw [hk']
    obtain ⟨a1, a2, a3⟩ := hsf.below.mats m hm
    exact ⟨by omega, by omega, by omega⟩
  · rw [hco']; exact hco
  · rw [hpad', hp] at hq; simp only [Option.some.injEq] at hq; subst hq; rw [hk']; omega
  · rw [hk']; omega
  · rw [hmats']; exact hok'.mats
  · rw [hpad']; exact hok'.pad
  · simp only [OsSt.cur, hcb', hco', pow_add, ← mul_assoc]
    rw [hag _ hcb]

/-! ## The rounds -/

theorem osRounds_k : ∀ (cp : Bool) (n i : ℕ) (st : OsSt), 5 ≤ st.k → st.k ≤ (osRounds cp i n st).2.k
  | _, 0, _, _, _ => le_rfl
  | cp, n + 1, i, st, h =>
    le_trans (osRound_k cp (n == 0) i st h)
      (osRounds_k false n (i + 1) _ (le_trans h (osRound_k cp (n == 0) i st h)))

theorem osRounds_pad : ∀ (cp : Bool) (n i : ℕ) (st : OsSt), (osRounds cp i n st).2.pad = st.pad
  | _, 0, _, _ => rfl
  | cp, n + 1, i, st => (osRounds_pad false n (i + 1) _).trans (osRound_state cp (n == 0) i st).2.2.1

theorem osRounds_cb : ∀ (cp : Bool) (n i : ℕ) (st : OsSt), (osRounds cp i n st).2.cb = st.cb
  | _, 0, _, _ => rfl
  | cp, n + 1, i, st => (osRounds_cb false n (i + 1) _).trans (osRound_state cp (n == 0) i st).1

theorem osRounds_mats : ∀ (cp : Bool) (n i : ℕ) (st : OsSt), (osRounds cp i n st).2.mats = st.mats
  | _, 0, _, _ => rfl
  | cp, n + 1, i, st => (osRounds_mats false n (i + 1) _).trans (osRound_state cp (n == 0) i st).2.2.2.1

/-- **The rounds' memory from what it holds for them**: their words at the cursor, the table,
the challenges' slots with the grinds passing (`RoundsMem`). -/
theorem roundsH_of {rd : Reader} {fch coefs tabs : E} (ht : WinTabs rd tabs) :
    ∀ (n i : ℕ) (fs : List E) (cl cur : E) (xs : List E), xs.length = 5 * n → ReadsAt rd cur xs →
      RoundsMem rd fch coefs n i fs cl xs → RoundsH rd fch coefs tabs n i fs cl cur xs
  | 0, _, _, _, _, _, _, _, _ => trivial
  | n + 1, i, fs, cl, cur, xs, hxl, hrd, ⟨hg, lg, la, lb, hm⟩ => by
    have hrd0 : ReadsAt rd cur (xs.take 5) := fun j hj ↦ by
      have := hrd j (by simp at hj; omega)
      simpa [List.getElem_take] using this
    have hrd1 : ReadsAt rd (cur * gen ^ 5) (xs.drop 5) := fun j hj ↦ by
      have := hrd (j + 5) (by simp at hj; omega)
      rw [loadHolds_mul_gen_pow, show 5 + j = j + 5 by ring]
      simpa [Nat.add_comm] using this
    rw [loadHolds_mul_gen_pow, Nat.add_zero] at lg la
    rw [loadHolds_mul_gen_pow] at lb
    exact ⟨hg, ⟨hrd0, ht, lg, la, lb⟩,
      roundsH_of ht n (i + 1) _ _ _ (xs.drop 5) (by simp [hxl]; omega) hrd1 hm⟩

/-- **`n` inline rounds as a block at fixed values.** -/
theorem osRounds_completeA (rd0 : Reader) (hl0 : LowDef 11 rd0) :
    ∀ (cp : Bool) (n i : ℕ) (st : OsSt) (σ : Val) (xs : List E), st.Sf → st.co + 5 * n < u128Bound →
      (∃ p, st.pad = some p) → (∀ C rd, HM M H C rd → st.Ok σ) → xs.length = 5 * n →
      (∀ C rd, HM M H C rd → RoundsH rd (σ (.n osFch)) (σ (.n osCoefs)) (σ (.n osTabs)) n i (st.fsv σ)
        (σ (.n st.claim)) (st.cur σ) xs) → (∀ C rd, H C rd → LowAgree rd rd0) →
      BlkA M H σ st.k (osRounds cp i n st).2.k (osRounds cp i n st).1
        (fun σ' ↦ RoundsOut σ σ' st (osRounds cp i n st).2
          (roundsTr n (st.fsv σ) (σ (.n st.claim)) xs) n ∧ AgreeBelow st.k σ σ') := by
  intro cp n
  induction n generalizing cp with
  | zero =>
    intro i st σ xs hsf hco _ hok _ _ _
    rw [show osRounds cp i 0 st = ([], st) from rfl]
    refine BlkA.of_ne fun ⟨C0, rd1, hH1⟩ ↦ BlkA.nil fun σ' ha ↦ ⟨?_, ha⟩
    obtain ⟨-, e2, e3, e4⟩ := OsSt.agree hsf.below ha
    exact ⟨by rw [e2]; rfl, by rw [e4]; simp, e3, hsf.fs, by simp, hsf.below,
      ((hok C0 rd1 hH1).agree ha).mats, rfl, le_rfl⟩
  | succ n ih =>
    intro i st σ xs hsf hco hpad hok hxl hR hag0
    refine BlkA.of_ne fun ⟨C0, rd1, hH1⟩ ↦ ?_
    set w := xs.take 5 with hw
    have hw5 : w.length = 5 := by simp [hw, hxl]
    have k33 := hsf.k
    have hk5 : 5 ≤ st.k := by omega
    have hA := osRound_completeA (M := M) (H := H) rd0 hl0 (cp := cp) (last := n == 0) (i := i) σ w hw5 hsf
      (by omega) hpad hok (hR C0 rd1 hH1).1 (fun C rd hH ↦ (hR C rd hH).2.1) hag0
    set st1 := (osRound cp (n == 0) i st).2 with hst1
    have hk1 : st.k ≤ st1.k := osRound_k _ _ _ _ hk5
    have hk2 : st1.k ≤ (osRounds false (i + 1) n st1).2.k := osRounds_k _ _ _ _ (le_trans hk5 hk1)
    have e : osRounds cp i (n + 1) st = ((osRound cp (n == 0) i st).1 ++ (osRounds false (i + 1) n st1).1,
        (osRounds false (i + 1) n st1).2) := rfl
    rw [e]
    set fsv := st.fsv σ with hfsv
    set cl := σ (.n st.claim) with hcl
    have hRt : roundsTr (n + 1) fsv cl xs =
        roundsTr n ((roundRets fsv 0 cl w).take 5) ((roundRets fsv 0 cl w).getD 6 0) (xs.drop 5) := rfl
    refine BlkA.mono (BlkA.seq hk1 hk2 hA fun σ1 ha1 ho1 ↦ ?_) fun σ' ⟨⟨_, ha'⟩, ho⟩ ↦ ⟨ho, ha'⟩
    obtain ⟨ro, _⟩ := ho1 C0 rd1 hH1
    have ef : st1.fsv σ1 = (roundRets fsv 0 cl w).take 5 := by
      have := congrArg Fs.cap ro.F
      simp only [OsSt.F] at this
      exact this
    have ec : σ1 (.n st1.claim) = (roundRets fsv 0 cl w).getD 6 0 := ro.claim
    have hih := ih false (i + 1) st1 σ1 (xs.drop 5) ro.ok.sf (by rw [ro.co]; omega)
      (by rw [ro.pad]; exact hpad) (fun _ _ _ ↦ ro.ok) (by simp [hxl]; omega) (fun C rd hH ↦ by
        rw [ef, ec, ro.cur, ha1 osFch (by simp only [osFch]; omega),
          ha1 osCoefs (by simp only [osCoefs]; omega), ha1 osTabs (by simp only [osTabs]; omega)]
        exact (hR C rd hH).2.2) hag0
    rw [ef, ec, ← hRt] at hih
    refine BlkA.monoH hih fun C rd hH σ' ha ⟨ho, _⟩ ↦ ⟨ho.F, ?_, ho.claim, ho.fs, ?_, ho.below, ho.mats,
      by rw [ho.pad, ro.pad], le_trans hk1 ho.k⟩
    · rw [ho.cur, ro.cur, mul_assoc, ← pow_add]
      ring_nf
    · rw [ho.co, ro.co]; ring

end
end LeanVM.Guest.B1.Whir
