/-
  LeanVM.Guest.B1.Main.RawAt

  `main`'s raw-signature loops `main_loop2` (leanXMSS) and `main_loop3` (leanSPHINCS) in the uniform
  placed form (`CompleteAtD`), over the raw signatures' honest data.
-/

module

public import LeanVM.Guest.B1.Main.RawCChk
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Lift.Sig
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Digest.CoverComplete
public import LeanVM.Guest.Data.NameStrings

/-!
# The raw-signature loops, placed

`RawXData nrx X cv tb Lin`: per raw leanXMSS signature `i < nrx`, its slot below `X` (the
leanXMSS region's size), the public key, message and signature (verifying), and on every memory
defined below `2^23` holding the caller's words `Lin`: the coverage word at `cv + slot i` is
`g^i`, the claim's four cells at `tb + 4·slot i`; those words are among `Lin`'s.
`RawSData nrs Y X nrx cv tb bb Lin`: per raw leanSPHINCS signature `j < nrs`, its slot below `Y`,
the coverage word at `cv + X + slot j` is `g^(nrx + j)`, the claim at `tb + 4·slot j`, the byte
table at `bb`.

Both loops place nothing (`raw3_pure`: `main_loop2`'s prelude and epilogue by evaluation, its inline
leanXMSS check `Sig.xSeg` a leaf); on such a memory each runs by a tree loading from `Lin` only
(`rawX_relIn`, `rawS_relIn`, by induction from the last iteration and `relIn_of_walk`), so they
are `CompleteAtD` (`completeAtD_of_relIn`): `rawX_completeAt`, `rawS_completeAt`, from every
counter below the count, with the arguments `main` passes (`main_loop2`'s: `l2ArgsAt`, the four
words and `main`'s tags `lxTagWords`).

An iteration of `main_loop2` (`rawX_step`) starts from `l2σ`, every value outside the check set
(parameters, prelude, epilogue: `lean_ethereum.py`); the check's completeness
(`Sig.verify_lean_xmss_complete_Spec`, the tags holding by `lxTagWords_hold`) changes only
`.n 66 ..< .n 120764`, so the prelude and the epilogue still hold (`offSeg`); its loads are the
cover word and the claim's four words (`l2_loads`, by `Lift.xSeg_leafOk` for the check), its one
call the next iteration (`l2_relIn_of_body`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (LowDef CompleteAtD Returns)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul)

@[expose] public section

/-! ## The data -/

/-- **The raw leanXMSS signatures' honest data.** -/
structure RawXData (nrx X cv tb : ℕ) (Lin : Layout) where
  slot : ℕ → ℕ
  pk : ℕ → HashSig.PublicKey
  msg : ℕ → HashSig.Message
  sig : ℕ → LeanXmss.Signature
  slot_lt : ∀ i < nrx, slot i < X
  verify : ∀ i < nrx, LeanXmss.verifyWithKeccak (pk i) (msg i) (sig i) = true
  cover : ∀ rd, LowDef 23 rd → MemL rd Lin → ∀ i < nrx, LoadHolds rd (gen ^ cv) (slot i) (gen ^ i)
  claim : ∀ rd, LowDef 23 rd → MemL rd Lin → ∀ i < nrx,
    Sig.ClaimAt rd (gen ^ (tb + 4 * slot i)) (Sig.cellOf128 (pk i).root)
      (Sig.cellOf128 (pk i).parameter) (Sig.cellOf128 ((msg i).extractLsb' 0 128))
      (Sig.cellOf128 ((msg i).extractLsb' 128 128))
  regCover : ∀ i < nrx, RegionL Lin (cv + slot i)
  regClaim : ∀ i < nrx, ∀ k < 4, RegionL Lin (tb + 4 * slot i + k)

/-- **The raw leanSPHINCS signatures' honest data.** -/
structure RawSData (nrs Y X nrx cv tb bb : ℕ) (Lin : Layout) where
  slot : ℕ → ℕ
  pk : ℕ → Sphincs.PublicKey
  msg : ℕ → HashSig.Message
  sig : ℕ → Sphincs.Signature
  slot_lt : ∀ j < nrs, slot j < Y
  verify : ∀ j < nrs, Sphincs.verifyWithKeccak (pk j) (msg j) (sig j) = true
  cover : ∀ rd, LowDef 23 rd → MemL rd Lin → ∀ j < nrs,
    LoadHolds rd (gen ^ cv) (X + slot j) (gen ^ (nrx + j))
  claim : ∀ rd, LowDef 23 rd → MemL rd Lin → ∀ j < nrs,
    Sig.ClaimAt rd (gen ^ (tb + 4 * slot j)) (Sig.cellOf128 (pk j).publicSeed)
      (Sig.cellOf128 (pk j).root) (Sig.cellOf128 ((msg j).extractLsb' 0 128))
      (Sig.cellOf128 ((msg j).extractLsb' 128 128))
  bytes : ∀ rd, LowDef 23 rd → MemL rd Lin → Sig.ByteBits rd (gen ^ bb)
  regCover : ∀ j < nrs, RegionL Lin (cv + (X + slot j))
  regClaim : ∀ j < nrs, ∀ k < 4, RegionL Lin (tb + 4 * slot j + k)
  regBytes : ∀ v < 256, RegionL Lin (bb + v)

/-! ## Shared -/

theorem l4Pre_straight : l4Pre.all Main.Stmt.straight = true := rfl

theorem gen4 (s : ℕ) : gen ^ s * gen ^ s * (gen ^ s * gen ^ s) = gen ^ (4 * s) := by
  simp only [← pow_add]; congr 1; ring

theorem low_read {rd : Reader} (hl : LowDef 23 rd) {e : ℕ} (he : e < 2 ^ 23) :
    LoadHolds rd (gen ^ e) 0 ((rd (addressOfIndex e)).getD 0) := by
  rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl he

theorem guard_taken {i n : ℕ} (hn : n < 2 ^ 34) (hi : i + 1 ≤ n) :
    decide (gen ^ i * word 2 0 + gen ^ n ≠ 0) = decide (i + 1 ≠ n) := by
  rw [word_gen, gen_pow_mul_gen]
  refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h ?_⟩
  exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)

/-! ## `main_loop2` -/

/-- The arguments `main` passes `main_loop2` at the counter `g^i`. -/
def l2ArgsAt (i nrx X cv tb : ℕ) : List E :=
  [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords

/-- `main_loop2`'s valuation at the counter `g^i`, outside the check (`.n 66 ..< .n 120764`): its
parameters, its prelude's values (`lean_ethereum.py`: slot `s`, its range check, the
cover word's pointer, the claim's pointer `lx_table · (g^s)^4`), its epilogue's (the next counter
and the self-call's guard). -/
noncomputable def l2σ (rd : Reader) (i nrx X cv tb s : ℕ) : Val := fun v =>
  if v.idx < 5 then [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb].getD v.idx 0
  else if v.idx < 56 then lxTagWords.getD (v.idx - 5) 0
  else if v.idx < 66 then
    [gen ^ s, ginvW, gen ^ X * ginvW, gen ^ (X - 1 - s), (rd (addressOfIndex s)).getD 0,
      (rd (addressOfIndex (X - 1 - s))).getD 0, gen ^ cv * gen ^ s, gen ^ s * gen ^ s,
      gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
      gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s))].getD (v.idx - 56) 0
  else if 120764 ≤ v.idx then
    [word 2 0, gen ^ i * word 2 0, gen ^ i * word 2 0 + gen ^ nrx, word 2 0,
      gen ^ i * word 2 0].getD (v.idx - 120764) 0
  else 0

theorem lxTagWords_length : lxTagWords.length = 51 := by
  simp only [lxTagWords, List.length_map]; decide

/-- `l2σ`'s parameters from `.n 1`: the arguments after the counter. -/
theorem l2σ_tail (rd : Reader) (i nrx X cv tb s : ℕ) :
    (List.range 55).map (fun j => l2σ rd i nrx X cv tb s (.n (j + 1))) =
      [gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords := by
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

theorem l2σ_params (rd : Reader) (i nrx X cv tb s : ℕ) :
    (fn% «main_loop2»).params.map (l2σ rd i nrx X cv tb s) = l2ArgsAt i nrx X cv tb := by
  rw [show (fn% «main_loop2»).params = l2Fn.params from rfl, l2Fn_params, List.map_map,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  exact congrArg (gen ^ i :: ·) (l2σ_tail rd i nrx X cv tb s)

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

theorem out_seq_assoc' : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append' (σ : Val) : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append' σ l l', out_seq_assoc']

/-- The values of a block lie off the check's `.n 66 ..< .n 120764`. -/
def offSeg (ss : List Stmt) : Bool :=
  (Stmt.valsList ss).all fun v => decide (v.idx < 66) || decide (120764 ≤ v.idx)

/-- `main_loop2`'s epilogue holds at `l2σ`, the self-call's next iteration in `C`. -/
theorem l2Post_holds {C : CallRel} {rd : Reader} {i nrx X cv tb s : ℕ} (hnrx : nrx < 2 ^ 34)
    (hi : i < nrx) (hnext : i + 1 < nrx → C name% «main_loop2» (l2ArgsAt (i + 1) nrx X cv tb) []) :
    Stmt.HoldsList C rd (l2σ rd i nrx X cv tb s) Sig.l2Post False (fun rs => rs = []) := by
  have ht : List.map (l2σ rd i nrx X cv tb s) (List.map (fun j => V.n (j + 1)) (List.range 55)) =
      [gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords := by
    rw [List.map_map]; exact l2σ_tail rd i nrx X cv tb s
  simp only [Sig.l2Post, Sig.cst, Sig.mulS, Sig.addS, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, l2σ]
  simp only [Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, ite_false, ite_true,
    List.getD_cons_zero, List.getD_cons_succ, le_refl, true_and, and_true]
  refine ⟨by rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _, fun hne => ?_⟩
  have hne' := of_decide_eq_true ((guard_taken hnrx (by omega)).symm.trans (decide_eq_true hne))
  have := hnext (by omega)
  rw [l2ArgsAt, List.cons_append] at this
  rw [ht, word_gen, gen_pow_mul_gen]
  exact this

/-- `main_loop2`'s prelude holds at `l2σ`: the slot's range check, the cover word. -/
theorem l2Pre_holds {C : CallRel} {nrx X cv tb : ℕ} {Lin : Layout} (D : RawXData nrx X cv tb Lin)
    (hX : X ≤ 2 ^ 23) {rd : Reader} (hl : LowDef 23 rd) (hL : MemL rd Lin) {i : ℕ} (hi : i < nrx)
    {next : Prop} (hn : next) :
    Stmt.HoldsList C rd (l2σ rd i nrx X cv tb (D.slot i)) Sig.l2Pre next (fun rs => rs = []) := by
  have hs := D.slot_lt i hi
  simp only [Sig.l2Pre, Sig.hintW, Sig.cst, Sig.mulS, Sig.loadS, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, l2σ]
  simp only [Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, ite_false, ite_true,
    List.getD_cons_zero, List.getD_cons_succ, true_and]
  refine ⟨⟨low_read hl (by omega), ?_, low_read hl (by omega)⟩, ?_, hn⟩
  · rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact D.cover rd hl hL i hi

/-- The loads of `main_loop2`'s body: the cover word (`.n 62`) and the claim (`.n 65`). -/
theorem l2_loads {Lin : Layout} {σ : Val} {c p : ℕ} (h62 : σ (.n 62) = gen ^ c)
    (h65 : σ (.n 65) = gen ^ p) (hc : RegionL Lin c) (hp : ∀ k < 4, RegionL Lin (p + k)) :
    (walk σ (fn% «main_loop2»).body).All fun e => ∀ A, e.loadAddr? σ = some A →
      ∃ k, A = addressOfIndex k ∧ RegionL Lin k := by
  rw [Sig.loop2_split, walk_append', walk_append']
  refine Out.all_seq (Out.all_seq ?_ ?_) ?_
  · simp only [Sig.l2Post, Sig.cst, Sig.mulS, Sig.addS, walk, walk1, Out.seq, Out.pre]
    split_ifs <;> simp [Out.All, Ev.loadAddr?]
  · have hw := Lift.walk_leafOk (σ := σ) Sig.xSeg Lift.xSeg_leafOk
    have hP : ∀ e, Lift.EvLeafOk Lift.segLoad e → ∀ A, e.loadAddr? σ = some A →
        ∃ k, A = addressOfIndex k ∧ RegionL Lin k := by
      intro e hok A hA
      obtain ⟨off, hoff, rfl⟩ := Lift.loads_seg (σ := σ) (es := [e])
        (fun e' he' => by rw [List.mem_singleton.mp he']; exact hok) A
        (by simp [loadAddrs, hA])
      exact ⟨p + off, by rw [h65, limb0_gen_pow_mul], hp off hoff⟩
    cases hwx : walk σ Sig.xSeg with
    | fall es => rw [hwx] at hw; exact fun e he => hP e (hw e he)
    | ret es vs => rw [hwx] at hw; exact fun e he => hP e (hw e he)
    | stuck => trivial
  · simp only [Sig.l2Pre, Sig.hintW, Sig.cst, Sig.mulS, Sig.loadS, walk, walk1, Out.seq, Out.pre,
      Out.All, List.append_nil, List.singleton_append]
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq, false_imp_iff, forall_const]
    intro A hA
    refine ⟨c, ?_, hc⟩
    rw [← hA, h62, limb0_gen_pow_mul]; rfl

/-- `main_loop2`'s relation in the region from a run of its body there, loading from the region. -/
theorem l2_relIn_of_body {rd : Reader} {R : ℕ → Prop} {σ : Val} {args : List E} {fn : Fn}
    (hf : coreProgram.find? name% «main_loop2» = some fn) (hpar : fn.params.map σ = args)
    (hbody : Stmt.HoldsList (coreProgram.RelIn rd R) rd σ fn.body False (fun rs => rs = []))
    (hall : (walk σ fn.body).All fun e => ∀ A, e.loadAddr? σ = some A →
      ∃ k, A = addressOfIndex k ∧ R k) :
    coreProgram.RelIn rd R name% «main_loop2» args [] := by
  have hsat := walk_sat (P := coreProgram) fn.body
    (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hbody
  cases hw : walk σ fn.body with
  | fall es => rw [hw] at hsat; exact hsat.2.elim
  | stuck => rw [hw] at hsat; exact hsat.elim
  | ret es vs =>
    rw [hw] at hsat hall
    obtain ⟨hok, hr⟩ := hsat
    refine relIn_of_walk coreProgram_wf hf hpar hw hr (fun e he => (hok e he).1)
      (fun A hA => ?_) (fun c hc ht => ?_)
    · obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
      exact hall e he A hea
    · obtain ⟨e, he, hec⟩ := List.mem_filterMap.mp hc
      cases e with
      | call f args rets =>
        simp only [Ev.call?, Option.some.injEq] at hec
        subst hec
        exact (hok _ he).2 f args rets rfl
      | skip f args =>
        simp only [Ev.call?, Option.some.injEq] at hec
        subst hec
        cases ht
      | _ => simp [Ev.call?] at hec

/-- **One iteration of `main_loop2` loads from the caller's words**, given the next one's. -/
theorem rawX_step (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 23) (hnrx : nrx < 2 ^ 34) {rd : Reader}
    (hl : LowDef 23 rd) (hL : MemL rd Lin) {i : ℕ} (hi : i < nrx)
    (hnext : i + 1 < nrx →
      coreProgram.RelIn rd (RegionL Lin) name% «main_loop2» (l2ArgsAt (i + 1) nrx X cv tb) []) :
    coreProgram.RelIn rd (RegionL Lin) name% «main_loop2» (l2ArgsAt i nrx X cv tb) [] := by
  have hs := D.slot_lt i hi
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
  obtain ⟨σ', hext, -, hseg⟩ := hc (coreProgram.RelIn rd (RegionL Lin)) rd _ (D.pk i) (D.msg i)
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
    rw [← l2σ_params rd i nrx X cv tb (D.slot i), show (fn% «main_loop2»).params = l2Fn.params from
        rfl,
      l2Fn_params]
    simp only [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    exact hext.apply (Or.inl (by simp at hk; omega))
  have hpost := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Post_holds (C := coreProgram.RelIn rd (RegionL Lin)) (rd := rd) (X := X) (cv := cv)
      (tb := tb) (s := D.slot i) hnrx hi hnext)
  have hpre := (Sig.holdsList_congr _ (hoff _ (by decide +kernel)) _ _).mp
    (l2Pre_holds (C := coreProgram.RelIn rd (RegionL Lin)) D hX hl hL hi
      (next := Stmt.HoldsList (coreProgram.RelIn rd (RegionL Lin)) rd σ' (Sig.xSeg ++ Sig.l2Post)
        False (fun rs => rs = [])) (by rw [holdsList_append]; exact hseg _ _ hpost))
  have hbody : Stmt.HoldsList (coreProgram.RelIn rd (RegionL Lin)) rd σ' (fn% «main_loop2»).body
      False
      (fun rs => rs = []) :=
    (congrArg (fun b => Stmt.HoldsList (coreProgram.RelIn rd (RegionL Lin)) rd σ' b False
      (fun rs => rs = [])) Sig.loop2_split).mpr ((holdsList_append _ _ _ _).mpr hpre)
  refine l2_relIn_of_body find_loop2 hpar hbody
    (l2_loads (c := cv + D.slot i) (p := tb + 4 * D.slot i) ?_ ?_ (D.regCover i hi)
      (D.regClaim i hi))
  · rw [hext.apply (by omega)]; show gen ^ cv * gen ^ D.slot i = _; rw [← pow_add]
  · rw [hext.apply (by omega)]; exact h65

set_option maxRecDepth 20000 in
/-- **`main_loop2` loads from the caller's words**, from every counter below the count. -/
theorem rawX_relIn (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 23) (hnrx : nrx < 2 ^ 34) {rd : Reader}
    (hl : LowDef 23 rd) (hL : MemL rd Lin) :
    ∀ i < nrx, coreProgram.RelIn rd (RegionL Lin) name% «main_loop2»
      ([gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords) [] := by
  have key : ∀ t i, i + 1 + t = nrx →
      coreProgram.RelIn rd (RegionL Lin) name% «main_loop2» (l2ArgsAt i nrx X cv tb) [] := by
    intro t
    induction t with
    | zero => intro i hi; exact rawX_step hc D hX hnrx hl hL (by omega) fun h => absurd h (by omega)
    | succ t ih =>
      intro i hi; exact rawX_step hc D hX hnrx hl hL (by omega) fun _ => ih (i + 1) (by omega)
  intro i hi
  exact key (nrx - i - 1) i (by omega)

/-- **`main_loop2` places nothing**: its prelude and epilogue by evaluation, the check a leaf. -/
theorem raw3_pure : coreProgram.PureIn [name% «main_loop2»] := by
  intro g hg fn hf
  rw [List.mem_singleton] at hg
  subst hg
  have hfn : fn% «main_loop2» = fn := Option.some.inj (find_loop2.symm.trans hf)
  have hb : fn.body = Sig.l2Pre ++ (Sig.xSeg ++ Sig.l2Post) := hfn ▸ Sig.loop2_split
  rw [hb]
  have hp : ∀ xs ys : List Stmt, Stmt.pureList [name% «main_loop2»] (xs ++ ys) =
      (Stmt.pureList [name% «main_loop2»] xs && Stmt.pureList [name% «main_loop2»] ys) := by
    intro xs ys
    induction xs with
    | nil => simp [Stmt.pureList]
    | cons x xs ih => simp only [List.cons_append, Stmt.pureList, ih, Bool.and_assoc]
  rw [hp, hp, Lift.leafOkList_pure _ _ Lift.xSeg_leafOk]
  decide +kernel

/-- **`main_loop2` is complete, placed**, from every counter below the count. -/
theorem rawX_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 23) (hnrx : nrx < 2 ^ 34) :
    ∀ i < nrx, CompleteAtD fs cert 23 name% «main_loop2» Lin
      ([gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords) (Returns []) := fun i hi =>
  Lift.completeAtD_of_relIn raw3_pure (by simp) fun rd hl hL => rawX_relIn hc D hX hnrx hl hL i hi

/-! ## `main_loop3` -/

/-- `main_loop3`'s valuation at the counter `g^j`. -/
noncomputable def l4σ (rd : Reader) (j nrs Y cv X nrx tb bb s : ℕ) : Val :=
  Val.ofArgs [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb,
    gen ^ s, ginvW, gen ^ Y * ginvW, gen ^ (Y - 1 - s), (rd (addressOfIndex s)).getD 0,
    (rd (addressOfIndex (Y - 1 - s))).getD 0, gen ^ nrx * gen ^ j,
    gen ^ (cv + X) * gen ^ s, gen ^ s * gen ^ s, gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
    gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), word 2 0, gen ^ j * word 2 0,
    gen ^ j * word 2 0 + gen ^ nrs, word 2 0, gen ^ j * word 2 0]

set_option maxRecDepth 20000 in
/-- **`main_loop3` loads from the caller's words**, from every counter below the count. -/
theorem rawS_relIn (hc : Sig.SphincsCompleteSpecs)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin)
    (hY : Y ≤ 2 ^ 23) (hnrs : nrs < 2 ^ 34) {rd : Reader} (hl : LowDef 23 rd) (hL : MemL rd Lin) :
    ∀ j < nrs, coreProgram.RelIn rd (RegionL Lin) name% «main_loop3»
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] [] := by
  have key : ∀ t j, j + 1 + t = nrs → coreProgram.RelIn rd (RegionL Lin) name% «main_loop3»
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] [] := by
    intro t
    induction t with
    | zero => ?_
    | succ t ih => ?_
    all_goals
      intro j hj
      have hs := D.slot_lt j (by omega)
      set s := D.slot j with hsd
      set σ := l4σ rd j nrs Y cv X nrx tb bb s with hσ
      have hw := Main.walk_straight σ [] l4Pre l4Pre_straight
      rw [← l4_body] at hw
      obtain ⟨-, -, -, hpc⟩ := Main.straight_parts σ _ l4Pre_straight
      refine relIn_of_walk coreProgram_wf l4_find (by rw [l4_params]; rfl) hw rfl
        (slEvs_holds fun st hst => ?_) (fun A hA => ?_) (fun c hcm ht => ?_)
      · simp only [l4Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
        rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl
        all_goals simp only [SlOk, Atom.Holds, hσ, l4σ, ofArgs_n, List.getD_cons_succ,
          List.getD_cons_zero]
        · refine ⟨low_read hl (by omega), ?_, low_read hl (by omega)⟩
          rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
        · rw [show gen ^ (cv + X) * gen ^ s = gen ^ cv * gen ^ (X + s) by
              rw [← pow_add, ← pow_add, Nat.add_assoc],
            show gen ^ nrx * gen ^ j = gen ^ (nrx + j) by rw [← pow_add], loadHolds_mul_gen_pow,
            Nat.add_zero]
          exact D.cover rd hl hL j (by omega)
        · rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _
      · rw [B1.loadAddrs_straight σ _ l4Pre_straight,
          show l4Pre.filterMap B1.Stmt.loadS = [(.n 14, 0)] from rfl] at hA
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hA
        subst hA
        refine ⟨cv + (X + s), ?_, D.regCover j (by omega)⟩
        show (gen ^ (cv + X) * gen ^ s).limb 0 * addressOfIndex 0 = _
        rw [← pow_add, Nat.add_assoc, limb0_gen_pow_mul]; rfl
      · rw [hpc, show l4Pre.filterMap Main.Stmt.callS =
          [(none, "verify_sig_lean_sphincs", [.n 17, .n 6], []),
          (some (.n 20), name% «main_loop3», [.n 22, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])]
          from rfl] at hcm
        simp only [List.map_cons, List.map_nil, Main.mkCall, List.mem_cons, List.not_mem_nil,
          or_false] at hcm
        rcases hcm with rfl | rfl
        · show coreProgram.RelIn rd (RegionL Lin) "verify_sig_lean_sphincs"
            [gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen ^ bb] []
          rw [gen4, ← pow_add]
          exact Lift.verify_sig_lean_sphincs_relIn hc (fun i hi => hl i (by omega))
            (D.bytes rd hl hL) (D.claim rd hl hL j (by omega)) (D.verify j (by omega))
            (fun k hk => ⟨tb + 4 * s + k, limb0_gen_pow_mul _ _, D.regClaim j (by omega) k hk⟩)
            (fun v hv => ⟨bb + v, limb0_gen_pow_mul _ _, D.regBytes v hv⟩)
        · simp only [decide_eq_true_eq] at ht
          change gen ^ j * word 2 0 + gen ^ nrs ≠ 0 at ht
          have ht' := of_decide_eq_true ((guard_taken hnrs (by omega)).symm.trans
            (decide_eq_true ht))
          show coreProgram.RelIn rd (RegionL Lin) name% «main_loop3»
            [gen ^ j * word 2 0, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb,
              gen ^ bb] []
          rw [word_gen, gen_pow_mul_gen]
          first
            | exact absurd hj (by omega)
            | exact ih (j + 1) (by omega)
  intro j hj
  exact key (nrs - j - 1) j (by omega)

/-- **`main_loop3` is complete, placed**, from every counter below the count. -/
theorem rawS_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hc : Sig.SphincsCompleteSpecs) {nrs Y X nrx cv tb bb : ℕ}
    {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23) (hnrs : nrs < 2 ^ 34) :
    ∀ j < nrs, CompleteAtD fs cert 23 name% «main_loop3» Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb]
      (Returns []) := fun j hj =>
  Lift.completeAtD_of_relIn raw4_pure (by simp) fun rd hl hL =>
    rawS_relIn hc D hY hnrs hl hL j hj

end
end LeanVM.Guest.B1.Main
