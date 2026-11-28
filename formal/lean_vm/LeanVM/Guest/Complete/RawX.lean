module

public import LeanVM.Guest.Complete.RawS
public import LeanVM.Guest.B1.Sig.XmssSigPops
public import LeanVM.Guest.B1.Sig.BlockPops
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Exact.MainLoop2
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop2»

/-!
# `main_loop2`, the raw leanXMSS signatures, complete

`main_loop2` inlines leanXMSS's check (`Sig.xSeg`) between a prelude (`Sig.l2Pre`: the raw index,
its range check, the coverage cell, the claim's pointer) and an epilogue (`Sig.l2Post`: the next
counter, the self-call). It takes no words of its own: from the counter `g^i`, on memories holding
each signature's coverage cell and claim (`RawXPre`), its tree pops, iteration by iteration, the
raw index then the check's entries (`l2Pops`), every node exact (`main_loop2_completes`; its body
has no computed hint, `main_loop2_exactFree`). Each iteration's valuation is the check's completing
one (`Sig.verify_lean_xmss_complete_pops`) from `l2σ`, the bus era's outside the check.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (lxTagWords lxTagVals l2Fn l2Fn_params find_loop2)
open LeanVM.Guest.B1.Digest (gen_pow_mul_ginv gen_pow_add_isInK ginvW)

@[expose] public section

set_option linter.constructorNameAsVariable false

/-- `main_loop2`'s arguments at the counter `g^i`: the count, the slots, the coverage table `cov`,
the claims' table `tbl`, the carried chain tags. -/
def l2Args (i nrx X : ℕ) (cov tbl : E) : List E := [gen ^ i, gen ^ nrx, gen ^ X, cov, tbl] ++ lxTagWords

/-- `main_loop2`'s valuation at the counter `g^i`, outside the check (`.n 66 ..< .n 119742`): its
parameters, its prelude's values (slot `s`, its range check, the coverage cell's pointer, the
claim's pointer `tbl · (g^s)^4`), its epilogue's (the next counter and the self-call's guard). -/
noncomputable def l2σ (rd : Reader) (i nrx X : ℕ) (cov tbl : E) (s : ℕ) : Val := fun v =>
  if v.idx < 5 then [gen ^ i, gen ^ nrx, gen ^ X, cov, tbl].getD v.idx 0
  else if v.idx < 56 then lxTagWords.getD (v.idx - 5) 0
  else if v.idx < 66 then
    [gen ^ s, ginvW, gen ^ X * ginvW, gen ^ (X - 1 - s), (rd (addressOfIndex s)).getD 0,
      (rd (addressOfIndex (X - 1 - s))).getD 0, cov * gen ^ s, gen ^ s * gen ^ s,
      gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
      tbl * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s))].getD (v.idx - 56) 0
  else if 119742 ≤ v.idx then
    [word 2 0, gen ^ i * word 2 0, gen ^ i * word 2 0 + gen ^ nrx, word 2 0,
      gen ^ i * word 2 0].getD (v.idx - 119742) 0
  else 0

theorem lxTagWords_length : lxTagWords.length = 51 := by
  simp only [lxTagWords, List.length_map]; decide

/-- `l2σ`'s parameters from `.n 1`: the arguments after the counter. -/
theorem l2σ_tail (rd : Reader) (i nrx X : ℕ) (cov tbl : E) (s : ℕ) :
    (List.range 55).map (fun j => l2σ rd i nrx X cov tbl s (.n (j + 1))) =
      [gen ^ nrx, gen ^ X, cov, tbl] ++ lxTagWords := by
  apply List.ext_getElem (by simp [lxTagWords_length])
  intro k h1 h2
  have hk : k < 55 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, l2σ]
  by_cases h4 : k < 4
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), List.getElem_append_left (by simpa using h4)]
    interval_cases k <;> rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      List.getElem_append_right (by simp; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lxTagWords_length]; omega),
      Option.getD_some]
    congr 1

theorem l2σ_params (rd : Reader) (i nrx X : ℕ) (cov tbl : E) (s : ℕ) :
    (fn% «main_loop2»).params.map (l2σ rd i nrx X cov tbl s) = l2Args i nrx X cov tbl := by
  rw [show (fn% «main_loop2»).params = l2Fn.params from rfl, l2Fn_params, List.map_map,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  exact congrArg (gen ^ i :: ·) (l2σ_tail rd i nrx X cov tbl s)

/-- `main`'s tags hold the carried chain indices. -/
theorem lxTagWords_hold : Sig.LxTagsHold (fun j => lxTagWords.getD j 0) := by
  intro i hi hc
  have hv : ∀ i < 58, Sig.lxTagCarried i = true →
      lxTagVals.getD (Sig.lxTagSlot i - 1) 0 = i ∧ Sig.lxTagSlot i - 1 < lxTagVals.length := by
    decide
  obtain ⟨e, hlt⟩ := hv i hi hc
  show (lxTagVals.map fun i => word i 0).getD (Sig.lxTagSlot i - 1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some, word_eOfNat,
    ← List.getD_eq_getElem _ 0 hlt, e]

/-- The values of a block lie off the check's `.n 66 ..< .n 119742`. -/
def offSeg (ss : List Stmt) : Bool :=
  (Stmt.valsList ss).all fun v => decide (v.idx < 66) || decide (119742 ≤ v.idx)

/-- `main_loop2`'s epilogue holds at `l2σ`, under the trivial call relation. -/
theorem l2Post_holds {rd : Reader} {i nrx X : ℕ} {cov tbl : E} {s : ℕ} :
    Stmt.HoldsList (fun _ _ _ => True) rd (l2σ rd i nrx X cov tbl s) Sig.l2Post False (fun rs => rs = []) := by
  simp only [Sig.l2Post, Sig.xEnd, Sig.cst, Sig.mulS, Sig.addS, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_nil, l2σ]
  simp only [Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, ite_false, ite_true,
    List.getD_cons_zero, List.getD_cons_succ, le_refl, true_and, and_true]
  exact ⟨by rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _, fun _ => trivial⟩

/-- `main_loop2`'s prelude holds at `l2σ`: the slot's range check, the coverage cell. -/
theorem l2Pre_holds {k : ℕ} {rd : Reader} (hl : LowDef k rd) {i nrx X : ℕ} {cov tbl : E} {s : ℕ}
    (hX : X ≤ 2 ^ k) (hs : s < X) (hcov : LoadHolds rd (cov * gen ^ s) 0 (gen ^ i)) {next : Prop} (hn : next) :
    Stmt.HoldsList (fun _ _ _ => True) rd (l2σ rd i nrx X cov tbl s) Sig.l2Pre next (fun rs => rs = []) := by
  simp only [Sig.l2Pre, Sig.hintW, Sig.cst, Sig.mulS, Sig.loadS, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, l2σ]
  simp only [Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, ite_false, ite_true,
    List.getD_cons_zero, List.getD_cons_succ, true_and]
  refine ⟨⟨low_read' hl (by omega), ?_, low_read' hl (by omega)⟩, hcov, hn⟩
  rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega

/-- `main_loop2`'s epilogue before its self-call. -/
def l2PostA : List Stmt := Sig.l2Post.take 5

/-- `main_loop2`'s self-call's arguments. -/
def l2TArgs : List V :=
  .n (val% «main_loop2» "s5#4") :: (List.range 55).map fun j => V.n (j + (val% «main_loop2» "bound"))

/-- `main_loop2`'s self-call. -/
def l2Call : Stmt := .callIf (.n (val% «main_loop2» "s5#2")) name% «main_loop2» l2TArgs

set_option maxRecDepth 100000 in
theorem l2_body_split : (fn% «main_loop2»).body = (Sig.l2Pre ++ Sig.xSeg ++ l2PostA) ++ [l2Call, .ret []] := by
  rw [Sig.loop2_split, List.append_assoc, List.append_assoc]
  rfl

theorem l2Pre_atoms : Sig.atomsOnly Sig.l2Pre = true := rfl
theorem l2PostA_atoms : Sig.atomsOnly l2PostA = true := rfl

theorem l2Pre_pops (rd : Reader) (σ : Val) :
    Sig.atomsPops rd σ Sig.l2Pre = [("raw_index", [σ (.n (val% «main_loop2» "idx@1"))])] := rfl
theorem l2PostA_pops (rd : Reader) (σ : Val) : Sig.atomsPops rd σ l2PostA = [] := rfl

/-- The raw leanXMSS signatures: per signature its coverage slot, key, message and signature. -/
structure RawXSigs where
  slot : ℕ → ℕ
  pk : ℕ → HashSig.PublicKey
  msg : ℕ → HashSig.Message
  sig : ℕ → LeanXmss.Signature

/-- Iteration `i`'s entries: its raw index, then its check's. -/
def l2Pops (D : RawXSigs) (i : ℕ) : List Pop :=
  ("raw_index", [gen ^ D.slot i]) :: Sig.xSegPops (D.pk i) (D.msg i) (D.sig i)

/-- What `main_loop2` reads: for each signature `i < nrx`, its coverage cell at `cov·g^slot`
holding `g^i` and its claim at `tbl·g^(4·slot)`. -/
def RawXPre (D : RawXSigs) (nrx : ℕ) (cov tbl : E) (rd : Reader) : Prop :=
  ∀ i < nrx, LoadHolds rd (cov * gen ^ D.slot i) 0 (gen ^ i) ∧
    Sig.ClaimAt rd (tbl * gen ^ (4 * D.slot i)) (Sig.cellOf128 (D.pk i).root)
      (Sig.cellOf128 (D.pk i).parameter) (Sig.cellOf128 ((D.msg i).extractLsb' 0 128))
      (Sig.cellOf128 ((D.msg i).extractLsb' 128 128))

/-- `main_loop2`'s completeness from the counter `g^i`: iterations `i ..< nrx`' entries, every node
exact. -/
def RawXPost (D : RawXSigs) (i nrx : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = (List.range' i (nrx - i)).flatMap (l2Pops D) ∧ t.Every (ExactAt coreProgram rd)

set_option maxRecDepth 100000 in
/-- **One iteration of `main_loop2` completes**, given its tail's completeness. -/
theorem l2_step {k : ℕ} (hk : 8 ≤ k) {nrx X : ℕ} (hX : X ≤ 2 ^ k) (hnrx : nrx < 2 ^ 34) (D : RawXSigs)
    (hs : ∀ i < nrx, D.slot i < X)
    (hv : ∀ i < nrx, LeanXmss.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (cov tbl : E) {i : ℕ}
    (hi : i < nrx)
    (htail : i + 1 < nrx → CallCompletes0 k name% «main_loop2» (l2Args (i + 1) nrx X cov tbl) []
      (RawXPre D nrx cov tbl) (RawXPost D (i + 1) nrx)) :
    CallCompletes0 k name% «main_loop2» (l2Args i nrx X cov tbl) [] (RawXPre D nrx cov tbl)
      (RawXPost D i nrx) := by
  refine callCompletes0_node fun rd hl hp => ?_
  have hsi := hs i hi
  set s := D.slot i with hsd
  set σ0 := l2σ rd i nrx X cov tbl s with hσ0
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
  have h65 : σ0 Sig.sSigner = tbl * gen ^ (4 * s) := by
    show tbl * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)) = _
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
  have hpar : (fn% «main_loop2»).params.map σ' = l2Args i nrx X cov tbl := by
    rw [← l2σ_params rd i nrx X cov tbl s, show (fn% «main_loop2»).params = l2Fn.params from rfl, l2Fn_params]
    simp only [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    exact hext.apply (Or.inl (by simp at hk; omega))
  -- the body holds
  have hpost := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Post_holds (rd := rd) (X := X) (cov := cov) (tbl := tbl) (s := s))
  have hpre := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Pre_holds (nrx := nrx) (tbl := tbl) hl hX hsi (hp i hi).1
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
  have hargs : l2TArgs.map σ' = l2Args (i + 1) nrx X cov tbl := by
    have e68 : σ' (.n (val% «main_loop2» "s5#4")) = gen ^ (i + 1) := by
      rw [hext.apply (by simp only [Sig.xEnd]; omega)]
      show gen ^ i * word 2 0 = _
      rw [word_gen, gen_pow_mul_gen]
    rw [l2TArgs, List.map_cons, e68, l2Args, List.cons_append, List.map_map, ← l2σ_tail rd i nrx X cov tbl s]
    exact congrArg _ (List.map_congr_left fun k hk => hext.apply (Or.inl (by simp at hk; omega)))
  -- the tail
  obtain ⟨t1, hk1, hb1, hp1', hx1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ' [⟨name% «main_loop2», l2TArgs, [],
        decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧
      t1.pops coreProgram rd = (List.range' (i + 1) (nrx - (i + 1))).flatMap (l2Pops D) ∧
      t1.Every (ExactAt coreProgram rd) := by
    by_cases hlt : i + 1 < nrx
    · obtain ⟨t1, hn, hv1, hb, hp', hx⟩ := htail hlt rd hl hp
      have htk : decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0) = true := by
        rw [e66, guard_taken hnrx (by omega)]; exact decide_eq_true (by omega)
      have hv1' : t1.Valid coreProgram rd (l2TArgs.map σ') [] := by rw [hargs]; exact hv1
      exact ⟨t1, kidsValid_cons_taken htk hn hv1' kidsValid_nil, hb, hp', hx⟩
    · have htk : decide (σ' (.n (val% «main_loop2» "s5#2")) ≠ 0) = false := by
        rw [e66, guard_taken hnrx (by omega)]; exact decide_eq_false (by omega)
      refine ⟨.phantom name% «main_loop2» (l2σ rd (i + 1) nrx X cov tbl 0),
        kidsValid_cons_skip htk find_loop2 (by rw [l2σ_params, hargs]) kidsValid_nil, ?_, ?_,
        Tree.every_phantom⟩
      · rw [Tree.BufsOk]; trivial
      · rw [Tree.pops, show nrx - (i + 1) = 0 by omega]; rfl
  have hk : Tree.KidsValid coreProgram rd σ' (calls es) [t1] := by rw [hcalls]; exact hk1
  refine ⟨σ', _, es, [], [t1], find_loop2, hpar, hw, rfl, hev, hk, ?_, ?_,
    every_exact_of_free main_loop2_exactFree (t := .node name% «main_loop2» σ' (allocs σ' es) [t1])
      ⟨_, find_loop2, hpar, es, [], hw, rfl, hev, hk⟩ rfl rd⟩
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

/-- **`main_loop2` completes** from every counter below the count, on memories defined below `2^k`
(`8 ≤ k`, the slots `X ≤ 2^k`): it pops each iteration's raw index and check's entries, every node
exact. -/
theorem main_loop2_completes {k : ℕ} (hk : 8 ≤ k) {nrx X : ℕ} (hX : X ≤ 2 ^ k) (hnrx : nrx < 2 ^ 34)
    (D : RawXSigs) (hs : ∀ i < nrx, D.slot i < X)
    (hv : ∀ i < nrx, LeanXmss.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (cov tbl : E) :
    ∀ i < nrx, CallCompletes0 k name% «main_loop2» (l2Args i nrx X cov tbl) [] (RawXPre D nrx cov tbl)
      (RawXPost D i nrx) := by
  have key : ∀ t i, i + 1 + t = nrx → CallCompletes0 k name% «main_loop2» (l2Args i nrx X cov tbl) []
      (RawXPre D nrx cov tbl) (RawXPost D i nrx) := by
    intro t
    induction t with
    | zero => intro i hi; exact l2_step hk hX hnrx D hs hv cov tbl (by omega) fun h => absurd h (by omega)
    | succ t ih => intro i hi; exact l2_step hk hX hnrx D hs hv cov tbl (by omega) fun _ => ih (i + 1) (by omega)
  intro i hi
  exact key (nrx - i - 1) i (by omega)

end
end LeanVM.Guest.Complete
