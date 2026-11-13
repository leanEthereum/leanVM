/-
  LeanVM.Guest.B1.Main.RawAtP

  `main_loop2` (leanXMSS) placed with its pops (`CompleteAtDP`): each iteration its raw index, then its signature's check's entries (`Sig.xSegPops`), iteration by iteration.
-/

module

public import LeanVM.Guest.B1.Main.RawAt
public import LeanVM.Guest.B1.Main.CompleteP
public import LeanVM.Guest.B1.Sig.XmssSigPops

/-!
# `main_loop2`, placed with its pops

`RawAt`'s proof of `rawX_step` with the trees: the body's walk at the completing valuation of `Sig.verify_lean_xmss_complete_pops` is the prelude's atoms, the check (`FallPops`), the epilogue's atoms and the self-call, so `relAtInP_of_walk_loop` places it, the loop placing nothing (`raw3_pure`).

* `l2Pops D i`: iteration `i`'s entries, its raw index `g^(slot i)` then the check's;
* `rawX_stepP`: an iteration, its tail's entries after its own;
* `rawX_loopP`, `rawX_completeAtDP`: the loop from the counter `g^i` pops iterations `i ..< nrx`' entries in order.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtDP Returns disj_nil)

@[expose] public section

/-- **Iteration `i`'s entries**: its raw index, then its signature's check's. -/
def l2Pops {nrx X cv tb : ℕ} {Lin : Layout} (D : RawXData nrx X cv tb Lin) (i : ℕ) : List Pop :=
  ("raw_index", [gen ^ D.slot i]) :: Sig.xSegPops (D.pk i) (D.msg i) (D.sig i)

theorem main_loop2_loop : coreProgram.loop name% «main_loop2» = true := by
  rw [Program.loop_of_find? find_loop2, Fn.loop, Sig.loop2_split, List.reverse_append, List.reverse_append,
    Da.fn_name_of_find find_loop2]
  simp only [Sig.l2Post, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rfl

/-- `main_loop2`'s epilogue before its self-call. -/
def l2PostA : List Stmt := Sig.l2Post.take 5

/-- `main_loop2`'s self-call. -/
def l2Call : Stmt :=
  .callIf (.n 120766) name% «main_loop2» (.n 120768 :: (List.range 55).map fun j => V.n (j + 1))

theorem l2_body_split : (fn% «main_loop2»).body = (Sig.l2Pre ++ Sig.xSeg ++ l2PostA) ++ [l2Call, .ret []] := by
  rw [Sig.loop2_split, List.append_assoc, List.append_assoc]
  rfl

theorem l2Pre_atoms : Sig.atomsOnly Sig.l2Pre = true := rfl
theorem l2PostA_atoms : Sig.atomsOnly l2PostA = true := rfl

theorem l2Pre_pops (rd : Reader) (σ : Val) : Sig.atomsPops rd σ Sig.l2Pre = [("raw_index", [σ (.n 56)])] := rfl
theorem l2PostA_pops (rd : Reader) (σ : Val) : Sig.atomsPops rd σ l2PostA = [] := rfl

/-- **One iteration of `main_loop2`, placed, with its pops**: its raw index and its check's, then its tail's `pt`
(`[]` after the last). -/
theorem rawX_stepP (fs : String → ℕ) (cert : String → V → ℕ) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 23) (hnrx : nrx < 2 ^ 34) {rd : Reader}
    (hl : LowDef 23 rd) (hL : MemL rd Lin) {i : ℕ} (hi : i < nrx) {fp c Bt m : ℕ} {pt : List Pop}
    (htail : if i + 1 < nrx then
        RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs name% «main_loop2») c Bt m
          name% «main_loop2» (l2ArgsAt (i + 1) nrx X cv tb) [] pt
      else Bt = fs name% «main_loop2» ∧ m = 0 ∧ pt = []) :
    RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c (fs name% «main_loop2» + Bt) m
      name% «main_loop2» (l2ArgsAt i nrx X cv tb) [] (l2Pops D i ++ pt) := by
  have hs := D.slot_lt i hi
  set T : CallRel := fun _ _ _ => True with hT
  have htag : Sig.LxTagsHold (fun j => l2σ rd i nrx X cv tb (D.slot i) (Sig.sTagParam j)) := by
    intro j hj hcj
    obtain ⟨h1, h2⟩ := Sig.lxTagSlot_spec j hj hcj
    have e : l2σ rd i nrx X cv tb (D.slot i) (Sig.sTagParam (Sig.lxTagSlot j - 1)) =
        lxTagWords.getD (Sig.lxTagSlot j - 1) 0 := by
      have e1 : ((Sig.sTagParam (Sig.lxTagSlot j - 1)).idx < 5) = False :=
        eq_false (by simp only [Sig.sTagParam]; omega)
      have e2 : ((Sig.sTagParam (Sig.lxTagSlot j - 1)).idx < 56) = True :=
        eq_true (by simp only [Sig.sTagParam]; omega)
      unfold l2σ
      rw [ite_eq_right_of_eq_false _ _ e1, ite_eq_left_of_eq_true _ _ e2]
      congr 1
      simp only [Sig.sTagParam]; omega
    exact e.trans (lxTagWords_hold j hj hcj)
  have h65 : l2σ rd i nrx X cv tb (D.slot i) Sig.sSigner = gen ^ (tb + 4 * D.slot i) := by
    show gen ^ tb * (gen ^ D.slot i * gen ^ D.slot i * (gen ^ D.slot i * gen ^ D.slot i)) = _
    rw [gen4, ← pow_add]
  obtain ⟨σ', hext, hpops, hseg⟩ := Sig.verify_lean_xmss_complete_pops T rd _ (D.pk i) (D.msg i)
    (D.sig i) (fun j hj => hl j (by omega)) htag (h65 ▸ D.claim rd hl hL i hi) (D.verify i hi)
  have hoff : ∀ ss, offSeg ss = true →
      ∀ v ∈ Stmt.valsList ss, l2σ rd i nrx X cv tb (D.slot i) v = σ' v := by
    intro ss h v hv
    have := List.all_eq_true.mp h v hv
    refine (hext v fun k h1 h2 e => ?_).symm
    subst e
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    omega
  have hpar : (fn% «main_loop2»).params.map σ' = l2ArgsAt i nrx X cv tb := by
    rw [← l2σ_params rd i nrx X cv tb (D.slot i), show (fn% «main_loop2»).params = l2Fn.params from rfl,
      l2Fn_params]
    simp only [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    exact hext.apply (Or.inl (by simp at hk; omega))
  -- the body holds
  have hpost := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Post_holds (C := T) (rd := rd) (X := X) (cv := cv) (tb := tb) (s := D.slot i) hnrx hi fun _ => trivial)
  have hpre := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Pre_holds (C := T) D hX hl hL hi
      (next := Stmt.HoldsList T rd σ' (Sig.xSeg ++ Sig.l2Post) False (fun rs => rs = []))
      (by rw [holdsList_append]; exact hseg _ _ hpost))
  have hbody : Stmt.HoldsList T rd σ' (fn% «main_loop2»).body False (fun rs => rs = []) :=
    (congrArg (fun b => Stmt.HoldsList T rd σ' b False (fun rs => rs = [])) Sig.loop2_split).mpr
      ((holdsList_append _ _ _ _).mpr hpre)
  -- the path
  have hF : FallPops rd σ' (Sig.l2Pre ++ Sig.xSeg ++ l2PostA)
      (Sig.atomsPops rd σ' Sig.l2Pre ++ Sig.xSegPops (D.pk i) (D.msg i) (D.sig i) ++ []) := by
    rw [← l2PostA_pops rd σ']
    exact ((Sig.fallPops_atoms σ' l2Pre_atoms).append (hpops σ' fun _ _ => rfl).1).append
      (Sig.fallPops_atoms σ' l2PostA_atoms)
  obtain ⟨es1, hw1, hc1, hp1⟩ := hF
  set ct : Ev := if σ' (.n 120766) = 0 then .skip name% «main_loop2» (.n 120768 :: (List.range 55).map fun j => V.n (j + 1))
    else .call name% «main_loop2» (.n 120768 :: (List.range 55).map fun j => V.n (j + 1)) [] with hct
  have hw : walk σ' (fn% «main_loop2»).body = .ret (es1 ++ [.inK (.n 120766), ct]) [] := by
    rw [l2_body_split, walk_append_fall' _ hw1]
    simp [walk, walk1, Out.seq, Out.pre, l2Call, hct]
  set es := es1 ++ [.inK (.n 120766), ct] with hes
  have hsat := walk_sat (P := coreProgram) (fn% «main_loop2»).body
    (coreProgram_wf _ (List.mem_of_find?_eq_some find_loop2)) hbody
  rw [hw] at hsat
  have hpure := walk_pure (σ := σ') (fn% «main_loop2»).body (raw3_pure _ (List.mem_singleton_self _) _ find_loop2)
  rw [hw] at hpure
  have hal : allocs σ' es = [] := allocs_pure hpure
  -- the guard
  have e66 : σ' (.n 120766) = gen ^ i * word 2 0 + gen ^ nrx := by rw [hext.apply (by omega)]; rfl
  have htk : decide (σ' (.n 120766) ≠ 0) = decide (i + 1 < nrx) := by
    rw [e66, guard_taken hnrx (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have hcalls : calls es = [] ++ [⟨name% «main_loop2», .n 120768 :: (List.range 55).map fun j => V.n (j + 1), [],
      decide (i + 1 < nrx)⟩] := by
    rw [hes, calls_append', hc1, ← htk, hct]
    by_cases h0 : σ' (.n 120766) = 0
    · rw [ite_eq_left h0, decide_eq_false (not_not.mpr h0)]; rfl
    · rw [ite_eq_right h0, decide_eq_true h0]; rfl
  have hargs : (V.n 120768 :: (List.range 55).map fun j => V.n (j + 1)).map σ' = l2ArgsAt (i + 1) nrx X cv tb := by
    have e68 : σ' (.n 120768) = gen ^ (i + 1) := by
      rw [hext.apply (by omega)]
      show gen ^ i * word 2 0 = _
      rw [word_gen, gen_pow_mul_gen]
    rw [List.map_cons, e68, l2ArgsAt, List.cons_append, List.map_map, ← l2σ_tail rd i nrx X cv tb (D.slot i)]
    exact congrArg _ (List.map_congr_left fun k hk => hext.apply (Or.inl (by simp at hk; omega)))
  -- the pops
  have hps : splice rd σ' es ([] ++ [pt]) = l2Pops D i ++ pt := by
    have e56 : σ' (.n 56) = gen ^ D.slot i := by rw [hext.apply (by omega)]; rfl
    rw [hes, splice_append_of_calls_nil _ _ hc1, hp1, l2Pre_pops, e56, List.append_nil]
    have : splice rd σ' [.inK (.n 120766), ct] [pt] = pt := by
      rw [hct]; split <;> simp [splice]
    rw [List.nil_append, this]
    rfl
  have h := relAtInP_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ') (rd := rd)
    coreProgram_wf (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (Rt := RegionL Lin)
    (Dt := RegionL []) (fp := fp) (c := c) (Bt := Bt) (m := m) (N := 0) (pss := []) (pt := pt)
    find_loop2 main_loop2_loop hpar hw rfl (fun e he => (hsat.1 e he).1) hcalls ?_
    (by rw [allocDsts_pure hpure, hal]; rfl)
    (fun q hq => by rw [addrs_pure hpure] at hq; simp at hq)
    ⟨rfl, fun _ h => h⟩ (fun j hj => Or.inl hj) ?_ (fun j hj => by simp [RegionL] at hj) hps
  · simp only [hal, List.sum_nil, Nat.zero_add, List.map_nil] at h; exact h
  · rw [hal, List.sum_nil, Nat.add_zero, Nat.add_zero, hargs]
    by_cases hn : i + 1 < nrx
    · simp only [hn, ↓reduceIte] at htail
      simp only [hn, decide_true, ↓reduceIte, List.map_nil]
      exact htail
    · simp only [hn, ↓reduceIte] at htail
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · intro A hA
    have hld := l2_loads (Lin := Lin) (σ := σ') (c := cv + D.slot i) (p := tb + 4 * D.slot i)
      (by rw [hext.apply (by omega)]; show gen ^ cv * gen ^ D.slot i = _; rw [← pow_add])
      (by rw [hext.apply (by omega)]; exact h65) (D.regCover i hi) (D.regClaim i hi)
    rw [hw] at hld
    obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    obtain ⟨k, hk, hr⟩ := hld e he A hea
    exact ⟨k, hk, Or.inr (Or.inl hr)⟩

/-- **`main_loop2` from the counter `g^i`, placed, with its pops**: iterations `i ..< nrx`' entries in order. -/
theorem rawX_loopP (fs : String → ℕ) (cert : String → V → ℕ) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 23) (hnrx : nrx < 2 ^ 34) {rd : Reader}
    (hl : LowDef 23 rd) (hL : MemL rd Lin) :
    ∀ i < nrx, ∀ fp c, RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c
      ((nrx - i + 1) * fs name% «main_loop2») 0 name% «main_loop2» (l2ArgsAt i nrx X cv tb) []
      ((List.range' i (nrx - i)).flatMap (l2Pops D)) := by
  suffices key : ∀ t i, i + 1 + t = nrx → ∀ fp c, RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c
      ((nrx - i + 1) * fs name% «main_loop2») 0 name% «main_loop2» (l2ArgsAt i nrx X cv tb) []
      ((List.range' i (nrx - i)).flatMap (l2Pops D)) from
    fun i hi => key (nrx - i - 1) i (by omega)
  intro t
  induction t with
  | zero =>
    intro i hi fp c
    have h := rawX_stepP fs cert D hX hnrx hl hL (i := i) (fp := fp) (c := c) (Bt := fs name% «main_loop2»)
      (m := 0) (pt := []) (by omega) (by rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact ⟨rfl, rfl, rfl⟩)
    rw [show nrx - i = 1 by omega, List.range'_one, List.flatMap_singleton, show (1 + 1) * fs name% «main_loop2» =
      fs name% «main_loop2» + fs name% «main_loop2» by ring]
    rw [List.append_nil] at h
    exact h
  | succ t ih =>
    intro i hi fp c
    have h := rawX_stepP fs cert D hX hnrx hl hL (i := i) (fp := fp) (c := c) (by omega)
      (by rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; exact ih (i + 1) (by omega) (fp + fs name% «main_loop2») c)
    rw [show nrx - i = nrx - (i + 1) + 1 by omega, List.range'_succ, List.flatMap_cons,
      show (nrx - (i + 1) + 1 + 1) * fs name% «main_loop2» =
        fs name% «main_loop2» + (nrx - (i + 1) + 1) * fs name% «main_loop2» by ring]
    exact h

/-- **`main_loop2` is complete, placed, with its pops**, from every counter `g^i` below the count: iterations
`i ..< nrx`' entries in order. -/
theorem rawX_completeAtDP (fs : String → ℕ) (cert : String → V → ℕ) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 23) (hnrx : nrx < 2 ^ 34) :
    ∀ i < nrx, CompleteAtDP fs cert 23 name% «main_loop2» Lin
      ([gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords) (Returns [])
      (fun _ => (List.range' i (nrx - i)).flatMap (l2Pops D)) := fun i hi fp =>
  ⟨(nrx - i + 1) * fs name% «main_loop2» + 0, [], [], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
    fun rd hl hL => (rawX_loopP fs cert D hX hnrx hl (by simpa using hL) i hi fp
      (fp + (nrx - i + 1) * fs name% «main_loop2»)).relAtInP⟩

end
end LeanVM.Guest.B1.Main
