/-
  LeanVM.Guest.Complete.RawXA

  `main_loop2`, the raw leanXMSS signatures, placed: its completeness with its shape, on memories
  defined where its range check reads.
-/

module

public import LeanVM.Guest.Complete.RawX
public import LeanVM.Guest.Complete.RawKit
public import LeanVM.Guest.Complete.MainCalleesA
public import LeanVM.Guest.Complete.RawX2.C0
public import LeanVM.Guest.Complete.RawX2.C1a
public import LeanVM.Guest.Complete.RawX2.C1b
public import LeanVM.Guest.Complete.RawX2.C2
public import LeanVM.Guest.Complete.RawX2.C3
public import LeanVM.Guest.Complete.RawX2.C4a
public import LeanVM.Guest.Complete.RawX2.C4b
public import LeanVM.Guest.Complete.RawX2.C5
public import LeanVM.Guest.Complete.RawX2.C6
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop2»

/-!
# `main_loop2`, placed

`main_loop2` places nothing, hints no heap word, loads only its coverage cell (`.n 62`) and its
claim's four cells (`.n 65`) and calls only itself (`l2_facts`, by chunks; `l2_pureIn`). So every
tree `l2_stepA` builds has its shape (`RawXPostA`): block `loopBlock` over the iterations left,
ending at its cursor, loading the coverage cells and the claims, which the caller hands it in `R`.
`l2_stepA` is `l2_step` with that shape and with the raw index's range check reading words defined
on the memories `P` admits (`∀ j < X, (rd (addressOfIndex j)).isSome`) rather than `X ≤ 2^k`
(the slots exceed `2^17` on large nodes). `l2_atEvery`: placed at every frame and cursor by
`callAtA_of_callCompletes0`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (lxTagWords l2Fn l2Fn_params find_loop2)
open LeanVM.Guest.B1.Digest (gen_pow_mul_ginv gen_pow_add_isInK ginvW)
open LeanVM.Guest.B1.VsC (LlShape)

@[expose] public section

set_option linter.constructorNameAsVariable false

/-! ## The body's facts -/

set_option maxRecDepth 100000 in
theorem l2_facts : Stmt.atomsAll (loadVarB l2Loads) (fn% «main_loop2»).body = true ∧
    Stmt.pureList [name% «main_loop2»] (fn% «main_loop2»).body = true := by
  rw [show (fn% «main_loop2»).body = Fn.«main_loop2».core.c0 ++ Fn.«main_loop2».core.c1 ++
      Fn.«main_loop2».core.c2 ++ Fn.«main_loop2».core.c3 ++ Fn.«main_loop2».core.c4 ++
      Fn.«main_loop2».core.c5 ++ Fn.«main_loop2».core.c6 from rfl,
    ← List.take_append_drop 3 Fn.«main_loop2».core.c1, ← List.take_append_drop 3 Fn.«main_loop2».core.c4]
  simp only [Stmt.atomsAll_append, pureList_append, l2_ck_c0.1, l2_ck_c0.2, l2_ck_c1a.1, l2_ck_c1a.2,
    l2_ck_c1b.1, l2_ck_c1b.2, l2_ck_c2.1, l2_ck_c2.2, l2_ck_c3.1, l2_ck_c3.2, l2_ck_c4a.1, l2_ck_c4a.2,
    l2_ck_c4b.1, l2_ck_c4b.2, l2_ck_c5.1, l2_ck_c5.2, l2_ck_c6.1, l2_ck_c6.2, Bool.and_self]
  exact ⟨trivial, trivial⟩

theorem l2_pureIn : coreProgram.PureIn [name% «main_loop2»] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_loop2] at hf
  obtain rfl := Option.some.inj hf
  exact l2_facts.2

theorem l2_loop : coreProgram.loop name% «main_loop2» = true := by decide +kernel

/-! ## The raw index's range check where the memory is defined -/

/-- `main_loop2`'s prelude holds at `l2σ`, its range check's words defined. -/
theorem l2Pre_holdsD {rd : Reader} {i nrx X : ℕ} {cov tbl : E} {s : ℕ} (hs : s < X)
    (hd : ∀ j < X, (rd (addressOfIndex j)).isSome) (hcov : LoadHolds rd (cov * gen ^ s) 0 (gen ^ i))
    {next : Prop} (hn : next) :
    Stmt.HoldsList (fun _ _ _ => True) rd (l2σ rd i nrx X cov tbl s) Sig.l2Pre next (fun rs => rs = []) := by
  simp only [Sig.l2Pre, Sig.hintW, Sig.cst, Sig.mulS, Sig.loadS, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, l2σ]
  simp only [Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, ite_false, ite_true,
    List.getD_cons_zero, List.getD_cons_succ, true_and]
  refine ⟨⟨read_def (hd s hs), ?_, read_def (hd _ (by omega))⟩, hcov, hn⟩
  rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega

/-! ## One iteration, with its shape -/

/-- `main_loop2`'s completeness from `g^i`, placed: `RawXPost`, its block over the iterations
left, ending at its cursor, loading and hinting in `R`. -/
def RawXPostA (al : String → Bool) (R : ℕ → Prop) (D : RawXSigs) (i nrx : ℕ) (rd : Reader) (t : Tree) : Prop :=
  RawXPost D i nrx rd t ∧ LlShape B2C.fs al (loopBlock name% «main_loop2» (nrx - i)) id R t

theorem phantom_shape {al : String → Bool} {R : ℕ → Prop} {L : String} {σ : Val} :
    LlShape B2C.fs al (loopBlock L 0) id R (.phantom L σ) := by
  refine ⟨?_, fun c => endA_phantom c L σ, by rw [Tree.LoadsR]; trivial, by rw [Tree.HintsR]; trivial⟩
  rw [Tree.block, loopBlock, Nat.zero_mul, Nat.zero_add]

set_option maxRecDepth 100000 in
/-- **One iteration of `main_loop2` completes, with its shape**, given its tail's. -/
theorem l2_stepA {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) {nrx X : ℕ} (hnrx : nrx < 2 ^ 34) (D : RawXSigs)
    (hs : ∀ i < nrx, D.slot i < X)
    (hv : ∀ i < nrx, LeanXmss.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (C T : ℕ) {R : ℕ → Prop}
    (hR : ∀ i < nrx, R (C + D.slot i) ∧ ∀ o < 4, R (T + 4 * D.slot i + o)) {P : Reader → Prop}
    (hP : ∀ rd, LowDef k rd → P rd →
      RawXPre D nrx (ptrAt C) (ptrAt T) rd ∧ ∀ j < X, (rd (addressOfIndex j)).isSome)
    {i : ℕ} (hi : i < nrx)
    (htail : i + 1 < nrx → CallCompletes0 k name% «main_loop2» (l2Args (i + 1) nrx X (ptrAt C) (ptrAt T)) []
      P (RawXPostA al R D (i + 1) nrx)) :
    CallCompletes0 k name% «main_loop2» (l2Args i nrx X (ptrAt C) (ptrAt T)) [] P (RawXPostA al R D i nrx) := by
  refine callCompletes0_node fun rd hl hP0 => ?_
  obtain ⟨hp, hd⟩ := hP rd hl hP0
  have hsi := hs i hi
  set s := D.slot i with hsd
  set σ0 := l2σ rd i nrx X (ptrAt C) (ptrAt T) s with hσ0
  have htag : Sig.LxTagsHold (fun j => σ0 (Sig.sTagParam j)) := by
    intro j hj hcj
    obtain ⟨h1, h2⟩ := Sig.lxTagSlot_spec j hj hcj
    have e : σ0 (Sig.sTagParam (Sig.lxTagSlot j - 1)) = lxTagWords.getD (Sig.lxTagSlot j - 1) 0 := by
      have e1 : ((Sig.sTagParam (Sig.lxTagSlot j - 1)).idx < 5) = False :=
        eq_false (by simp only [Sig.sTagParam]; omega)
      have e2 : ((Sig.sTagParam (Sig.lxTagSlot j - 1)).idx < 56) = True :=
        eq_true (by simp only [Sig.sTagParam]; omega)
      rw [hσ0]; unfold l2σ
      rw [ite_eq_right_of_eq_false _ _ e1, ite_eq_left_of_eq_true _ _ e2]
      congr 1
      simp only [Sig.sTagParam]; omega
    exact e.trans (lxTagWords_hold j hj hcj)
  have h65 : σ0 Sig.sSigner = ptrAt T * gen ^ (4 * s) := by
    show ptrAt T * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)) = _
    rw [gen4]
  have hm : Sig.MemOK rd 256 := fun j hj => hl.mono hk j (by norm_num; omega)
  obtain ⟨σ', hext, hpops, hseg⟩ := Sig.verify_lean_xmss_complete_pops (fun _ _ _ => True) rd σ0 (D.pk i)
    (D.msg i) (D.sig i) hm htag (h65 ▸ (hp i hi).2) (hv i hi)
  have hoff : ∀ ss, offSeg ss = true → ∀ v ∈ Stmt.valsList ss, σ0 v = σ' v := by
    intro ss h v hv'
    have := List.all_eq_true.mp h v hv'
    refine (hext v fun k h1 h2 e => ?_).symm
    subst e
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    simp only [Sig.xEnd] at h1 h2
    omega
  have hpar : (fn% «main_loop2»).params.map σ' = l2Args i nrx X (ptrAt C) (ptrAt T) := by
    rw [← l2σ_params rd i nrx X (ptrAt C) (ptrAt T) s, show (fn% «main_loop2»).params = l2Fn.params from rfl,
      l2Fn_params]
    simp only [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    exact hext.apply (Or.inl (by simp at hk; omega))
  -- the body holds
  have hpost := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Post_holds (rd := rd) (X := X) (cov := ptrAt C) (tbl := ptrAt T) (s := s))
  have hpre := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Pre_holdsD (nrx := nrx) (tbl := ptrAt T) hsi hd (hp i hi).1
      (next := Stmt.HoldsList (fun _ _ _ => True) rd σ' (Sig.xSeg ++ Sig.l2Post) False (fun rs => rs = []))
      (by rw [holdsList_append]; exact hseg _ _ hpost))
  have hbody : Stmt.HoldsList (fun _ _ _ => True) rd σ' (fn% «main_loop2»).body False (fun rs => rs = []) :=
    (congrArg (fun b => Stmt.HoldsList (fun _ _ _ => True) rd σ' b False (fun rs => rs = [])) Sig.loop2_split).mpr
      ((holdsList_append _ _ _ _).mpr hpre)
  -- the path
  have hF : FallPops rd σ' (Sig.l2Pre ++ Sig.xSeg ++ l2PostA)
      (Sig.atomsPops rd σ' Sig.l2Pre ++ Sig.xSegPops (D.pk i) (D.msg i) (D.sig i) ++ []) := by
    rw [← l2PostA_pops rd σ']
    exact ((Sig.fallPops_atoms σ' l2Pre_atoms).append (hpops σ' fun _ _ => rfl).1).append
      (Sig.fallPops_atoms σ' l2PostA_atoms)
  obtain ⟨es1, hw1, hc1, hp1⟩ := hF
  set ct : Ev := if σ' (.n (val% «main_loop2» "s5#2")) = 0 then .skip name% «main_loop2» l2TArgs
    else .call name% «main_loop2» l2TArgs [] with hct
  have hw : walk σ' (fn% «main_loop2»).body = .ret (es1 ++ [.inK (.n (val% «main_loop2» "s5#2")), ct]) [] := by
    rw [l2_body_split, walk_append_fall' _ hw1]
    simp [walk, walk1, Out.seq, Out.pre, l2Call, hct]
  set es := es1 ++ [.inK (.n (val% «main_loop2» "s5#2")), ct] with hes
  have hsat := walk_sat (P := coreProgram) (fn% «main_loop2»).body
    (coreProgram_wf _ (List.mem_of_find?_eq_some find_loop2)) hbody
  rw [hw] at hsat
  have hev : ∀ e ∈ es, e.Holds rd σ' := fun e he => (hsat.1 e he).1
  -- the guard
  have e66 : σ' (.n (val% «main_loop2» "s5#2")) = gen ^ i * word 2 0 + gen ^ nrx := by
    rw [hext.apply (by simp only [Sig.xEnd]; omega)]; rfl
  have hcalls : calls es = [⟨name% «main_loop2», l2TArgs, [],
      decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0)⟩] := by
    rw [hes, calls_append', hc1, List.nil_append, hct]
    by_cases h0 : σ' (.n (val% «main_loop2» "s5#2")) = 0
    · rw [ite_eq_left h0, decide_eq_false (not_not.mpr h0)]; rfl
    · rw [ite_eq_right h0, decide_eq_true h0]; rfl
  have hargs : l2TArgs.map σ' = l2Args (i + 1) nrx X (ptrAt C) (ptrAt T) := by
    have e68 : σ' (.n (val% «main_loop2» "s5#4")) = gen ^ (i + 1) := by
      rw [hext.apply (by simp only [Sig.xEnd]; omega)]
      show gen ^ i * word 2 0 = _
      rw [word_gen, gen_pow_mul_gen]
    rw [l2TArgs, List.map_cons, e68, l2Args, List.cons_append, List.map_map,
      ← l2σ_tail rd i nrx X (ptrAt C) (ptrAt T) s]
    exact congrArg _ (List.map_congr_left fun k hk => hext.apply (Or.inl (by simp at hk; omega)))
  -- the tail
  obtain ⟨t1, hk1, hb1, hp1', hx1, hsh1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ' [⟨name% «main_loop2», l2TArgs, [],
        decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧
      t1.pops coreProgram rd = (List.range' (i + 1) (nrx - (i + 1))).flatMap (l2Pops D) ∧
      t1.Every (ExactAt coreProgram rd) ∧
      LlShape B2C.fs al (loopBlock name% «main_loop2» (nrx - (i + 1))) id R t1 := by
    by_cases hlt : i + 1 < nrx
    · obtain ⟨t1, hn, hv1, hb, ⟨hp', hx⟩, hsh⟩ := htail hlt rd hl hP0
      have htk : decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0) = true := by
        rw [e66, guard_taken hnrx (by omega)]; exact decide_eq_true (by omega)
      have hv1' : t1.Valid coreProgram rd (l2TArgs.map σ') [] := by rw [hargs]; exact hv1
      exact ⟨t1, kidsValid_cons_taken htk hn hv1' kidsValid_nil, hb, hp', hx, hsh⟩
    · have htk : decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0) = false := by
        rw [e66, guard_taken hnrx (by omega)]; exact decide_eq_false (by omega)
      refine ⟨.phantom name% «main_loop2» (l2σ rd (i + 1) nrx X (ptrAt C) (ptrAt T) 0),
        kidsValid_cons_skip htk find_loop2 (by rw [l2σ_params, hargs]) kidsValid_nil, ?_, ?_,
        Tree.every_phantom, ?_⟩
      · rw [Tree.BufsOk]; trivial
      · rw [Tree.pops, show nrx - (i + 1) = 0 by omega]; rfl
      · rw [show nrx - (i + 1) = 0 by omega]; exact phantom_shape
  have hk : Tree.KidsValid coreProgram rd σ' (calls es) [t1] := by rw [hcalls]; exact hk1
  -- the shape
  have hpure : ∀ e ∈ es, e.pure [name% «main_loop2»] := by
    have := walk_pure (σ := σ') _ l2_facts.2
    rwa [hw] at this
  have halloc : allocs σ' es = [] := allocs_pure hpure
  have e62 : σ' (.n 62) = ptrAt (C + s) := by
    rw [hext.apply (by omega), ← ptrAt_mul_gen_pow]; rfl
  have e65 : σ' (.n 65) = ptrAt (T + 4 * s) := by
    rw [hext.apply (by omega), ← ptrAt_mul_gen_pow, ← h65]; rfl
  have hptrs : ∀ q ∈ l2Loads, ∃ b, σ' (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o) := by
    intro q hq
    simp only [l2Loads, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨C + s, e62, fun o ho => by
        rw [show o = 0 by omega, Nat.add_zero]; exact (hR i hi).1⟩
    · exact ⟨T + 4 * s, e65, fun o ho => (hR i hi).2 o ho⟩
  have hown := loads_of_loadVarB l2_facts.1 hw hptrs
  have hev' : (Memory.Tree.node name% «main_loop2» σ' (allocs σ' es) [t1]).events coreProgram = es :=
    events_node find_loop2 hw
  refine ⟨σ', _, es, [], [t1], find_loop2, hpar, hw, rfl, hev, hk, ?_, ⟨?_,
    every_exact_of_free main_loop2_exactFree (t := .node name% «main_loop2» σ' (allocs σ' es) [t1])
      ⟨_, find_loop2, hpar, es, [], hw, rfl, hev, hk⟩ rfl rd⟩, ?_, ?_, ?_, ?_⟩
  · rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hb1, trivial⟩
  · have e56 : σ' (.n (val% «main_loop2» "idx@1")) = gen ^ s := by rw [hext.apply (by omega)]; rfl
    have hct' : splice rd σ' [.inK (.n (val% «main_loop2» "s5#2")), ct] [t1.pops coreProgram rd] =
        t1.pops coreProgram rd := by
      rw [hct]; split <;> simp [splice]
    rw [pops_node find_loop2 hw, Tree.popsKids, Tree.popsKids, hes, splice_append_of_calls_nil _ _ hc1, hp1,
      l2Pre_pops, e56, List.append_nil, hct', hp1', show nrx - i = nrx - (i + 1) + 1 by omega,
      List.range'_succ, List.flatMap_cons]
    rfl
  · rw [Tree.block]
    simp only [l2_loop, ↓reduceIte, Tree.blockLast, hsh1.1, loopBlock]
    rw [show nrx - i = nrx - (i + 1) + 1 by omega, Nat.succ_mul]
    omega
  · intro c
    rw [endA_node]
    simp only [l2_loop, ↓reduceIte, halloc, List.sum_nil, Nat.add_zero, endL_one, hsh1.2.1 c]
  · rw [Tree.LoadsR, hev', Tree.LoadsRKids, Tree.LoadsRKids]
    exact ⟨hown.1, hsh1.2.2.1, trivial⟩
  · rw [Tree.HintsR, hev', Tree.HintsRKids, Tree.HintsRKids]
    exact ⟨hown.2, hsh1.2.2.2, trivial⟩

/-- **`main_loop2` completes with its shape** from every counter below the count. -/
theorem main_loop2_completesA {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) {nrx X : ℕ} (hnrx : nrx < 2 ^ 34)
    (D : RawXSigs) (hs : ∀ i < nrx, D.slot i < X)
    (hv : ∀ i < nrx, LeanXmss.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (C T : ℕ) {R : ℕ → Prop}
    (hR : ∀ i < nrx, R (C + D.slot i) ∧ ∀ o < 4, R (T + 4 * D.slot i + o)) {P : Reader → Prop}
    (hP : ∀ rd, LowDef k rd → P rd →
      RawXPre D nrx (ptrAt C) (ptrAt T) rd ∧ ∀ j < X, (rd (addressOfIndex j)).isSome) :
    ∀ i < nrx, CallCompletes0 k name% «main_loop2» (l2Args i nrx X (ptrAt C) (ptrAt T)) [] P
      (RawXPostA al R D i nrx) := by
  have key : ∀ t i, i + 1 + t = nrx → CallCompletes0 k name% «main_loop2» (l2Args i nrx X (ptrAt C) (ptrAt T)) []
      P (RawXPostA al R D i nrx) := by
    intro t
    induction t with
    | zero => intro i hi; exact l2_stepA hk hnrx D hs hv C T hR hP (by omega) fun h => absurd h (by omega)
    | succ t ih => intro i hi; exact l2_stepA hk hnrx D hs hv C T hR hP (by omega) fun _ => ih (i + 1) (by omega)
  intro i hi
  exact key (nrx - i - 1) i (by omega)

/-- **`main_loop2` placed**: from its first iteration, at every frame and every cursor, ending at
the cursor, its block over its `nrx` iterations. -/
theorem l2_atEvery {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) {nrx X : ℕ} (hnrx : nrx < 2 ^ 34) (h0 : 0 < nrx)
    (D : RawXSigs) (hs : ∀ i < nrx, D.slot i < X)
    (hv : ∀ i < nrx, LeanXmss.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (C T : ℕ) {R : ℕ → Prop}
    (hR : ∀ i < nrx, R (C + D.slot i) ∧ ∀ o < 4, R (T + 4 * D.slot i + o)) {P : Reader → Prop}
    (hP : ∀ rd, LowDef k rd → P rd →
      RawXPre D nrx (ptrAt C) (ptrAt T) rd ∧ ∀ j < X, (rd (addressOfIndex j)).isSome) (lo : ℕ) :
    AtEveryB al k name% «main_loop2» (l2Args 0 nrx X (ptrAt C) (ptrAt T)) [] R P (RawXPost D 0 nrx)
      (loopBlock name% «main_loop2» nrx) lo (2 ^ 60) (2 ^ 40) := by
  intro fp cur _ _
  refine ⟨cur, fun _ => Nat.le_add_right _ _, (callAtA_of_callCompletes0 (fs := B2C.fs) (al := al) (cert := B2C.cert) l2_pureIn
    (List.mem_singleton_self _) le_rfl (main_loop2_completesA hk hnrx D hs hv C T hR hP 0 h0)
    fun rd t _ _ _ _ _ hq => ⟨by simpa using hq.2.1, hq.2.2.1 cur, hq.2.2.2.1, hq.2.2.2.2⟩).mono
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) fun _ _ _ hq => hq.1⟩

end
end LeanVM.Guest.Complete
