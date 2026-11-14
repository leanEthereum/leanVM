/-
  LeanVM.Guest.B1.Main.L5RPops

  `main`'s children loop on route R: `MainGoalsRR.l5` from its callees' trees on the memory (`mainGoalL5TBR`), each
  child's claim lists popping their entries and `verify_sub` the child's hints, stream by stream; and `MainSegs.kids`.
-/

module

public import LeanVM.Guest.B1.Main.L5R
public import LeanVM.Guest.B1.Main.L5Segs
public import LeanVM.Guest.B1.Main.MainPopsKids
public import LeanVM.Guest.Budget.FinalP
public import LeanVM.Guest.B1.Main.MainGoalsDaAgR

/-!
# The children loop with its pops

* `l5From_popsS`: `l5From_pops`, `verify_sub`'s trees popping their entries stream by stream;
* `L5From.mono`: the callees' predicates weakened;
* `l5PopsH`: the children loop's honest entries, each child's `l5Seg` at its claim lists' `px c`, `ps c` and
  `verify_sub`'s `pv c`;
* `mainGoalsRR_l5`: `MainGoalsRR.l5`, `q` popping `l5PopsH`; `mainSegs_kids`: `MainSegs.kids` for it, the claim lists
  popping the child's slots' pushes and `verify_sub` its hints past the advised sizes.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1 (LowDef CompleteAtDTB CompleteAtDTBR Returns)
open LeanVM.Guest.B1.Digest (valid_holds words_heap monoIs monoIs_sound genMulOk genMul_sound isAddAt add_sound
  atomsIn atoms_of_flat holdsList_flat)

@[expose] public section

section
variable {rd : Reader}

/-- **`l5From_pops` stream by stream**: `verify_sub`'s trees popping `pv` stream by stream. -/
theorem l5From_popsS {ex es : ℕ → ℕ} {Pxs Pss Pvs : ℕ → Tree → Prop} {px ps pv : ℕ → List Pop}
    {defer : ℕ → List E} {da : ℕ → E × E}
    (hpx : ∀ c t, Pxs c t → t.pops coreProgram rd = px c) (hps : ∀ c t, Pss c t → t.pops coreProgram rd = ps c)
    (hpv : ∀ c t, Pvs c t → SameStreams (t.pops coreProgram rd) (pv c))
    {nk Cr D : ℕ} {rest : List E} (hnk34 : nk < 2 ^ 34) (hnk : rest.getD 0 0 = gen ^ nk)
    (hCr : rest.getD 8 0 = gen ^ Cr) (hD : rest.getD 9 0 = gen ^ D)
    (hmem : ∀ c < nk, (defer c).length = 24 ∧ ReadsAt rd (gen ^ (Cr + 24 * c)) (defer c) ∧
      LoadHolds rd (gen ^ D) (2 * c) (da c).1 ∧ LoadHolds rd (gen ^ D) (2 * c + 1) (da c).2) :
    ∀ m c (t : Tree) (rets : List E), c + m = nk → t.Valid coreProgram rd (gen ^ c :: rest) rets →
      L5From ex es Pxs Pss Pvs m c t →
      SameStreams (t.pops coreProgram rd) ((List.range' c m).flatMap fun c =>
        l5Seg (ex c) (es c) (px c) (ps c) (defer c) (da c) (pv c)) := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ m ih =>
  intro c t rets hcm hv hL
  obtain ⟨σ, bufs, ks, rfl, h18, h19, hcl, hK⟩ := hL
  obtain ⟨fn0, hf0, hp0, hb⟩ := valid_holds hv
  rw [find_l5] at hf0
  obtain rfl := Option.some.inj hf0
  obtain ⟨fn', hf', -, es', vs, hw, -, -, hkv⟩ := hv
  rw [find_l5] at hf'
  obtain rfl := Option.some.inj hf'
  have hw' : walk σ (coreProgram.getD idx% «main_loop4» default).body = .ret (l5Evs σ) [] := by
    rw [l5_body, ← l5Body, l5Body_split]
    exact Main.walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [hw'] at hw
  cases hw
  rw [hcl] at hkv
  -- the valuation
  have hpar : ((List.range 16).map V.n).map σ = gen ^ c :: rest := by rw [← l5_params]; exact hp0
  have pr : ∀ i (hi : i < 16), σ (.n i) = (gen ^ c :: rest).getD i 0 := by
    intro i hi
    rw [← hpar, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have hrest : ((List.range 16).map V.n).tail.map σ = rest := by
    have := congrArg List.tail hpar
    rwa [← List.map_tail] at this
  have h0 : σ (.n 0) = gen ^ c := pr 0 (by omega)
  have h1 : σ (.n 1) = gen ^ nk := (pr 1 (by omega)).trans hnk
  have h9 : σ (.n 9) = gen ^ Cr := (pr 9 (by omega)).trans hCr
  have h10 : σ (.n 10) = gen ^ D := (pr 10 (by omega)).trans hD
  rw [l5_body, holdsList_append] at hb
  obtain ⟨hflat, hm33, hm35, hg55, hg52, ha53⟩ := l5_chk
  obtain ⟨hall, -⟩ := holdsList_flat _ hflat _ _ hb
  have hat := atoms_of_flat hall
  have h33 : σ (.n 33) = gen ^ (Cr + 24 * c) := by
    rw [monoIs_sound hm33 hat, h9, h0, ← pow_mul, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have h35 : σ (.n 35) = gen ^ (D + 2 * c) := by
    rw [monoIs_sound hm35 hat, h10, h0, ← pow_mul, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have h55 : σ (.n 55) = gen ^ (c + 1) := by rw [genMul_sound hg55 hat, h0, pow_succ]
  have h53 : σ (.n 53) = gen ^ (c + 1) + gen ^ nk := by
    rw [add_sound ha53 hat, genMul_sound hg52 hat, h0, h1, pow_succ]
  obtain ⟨hdl, hdef, hd0, hd1⟩ := hmem c (by omega)
  have hda : ReadsAt rd (gen ^ (D + 2 * c)) [(da c).1, (da c).2] := by
    intro k hk
    rw [pow_add, loadHolds_mul_gen_pow]
    match k, hk with
    | 0, _ => exact hd0
    | 1, _ => exact hd1
  -- the callees
  obtain ⟨kx, ks', kst, kv, kt, rfl⟩ : ∃ kx ks' kst kv kt, ks = [kx, ks', kst, kv, kt] := by
    have := kidsValid_len hkv
    simp only [l5CallList, List.length_cons, List.length_nil] at this
    match ks, this with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  obtain ⟨-, -, -, -, hn3, hv3, -, -, -, hvt, -⟩ := hkv
  obtain ⟨hTx, hTs, -, hTv, hTt, -⟩ := hK
  have px' := hpx c kx (hTx rfl)
  have ps' := hps c ks' (hTs rfl)
  have pv' := hpv c kv (hTv rfl)
  have pst : kst.pops coreProgram rd = [] := pops_nil_of_noWitness statement_digest_noWit
    (show kst.Valid coreProgram rd _ _ from hv3) hn3 rd
  have pt : SameStreams (kt.pops coreProgram rd) ((List.range' (c + 1) m).flatMap fun c =>
      l5Seg (ex c) (es c) (px c) (ps c) (defer c) (da c) (pv c)) := by
    by_cases h0' : σ (.n 53) = 0
    · have hcm' : c + 1 = nk := by
        rw [h53] at h0'
        exact Digest.gen_pow_inj' (by omega) hnk34 (e_add_eq_zero_iff.mp h0')
      rw [show m = 0 by omega, List.range'_zero, List.flatMap_nil]
      have : (decide (σ (.n 53) ≠ 0)) = false := by simpa using h0'
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hvt
      obtain ⟨⟨g, σ', rfl⟩, -⟩ := hvt
      exact SameStreams.refl _
    · have ht : (decide (σ (.n 53) ≠ 0)) = true := by simpa using h0'
      simp only [ht, ↓reduceIte] at hvt
      rw [l5_tail_args, h55, hrest] at hvt
      exact ih (c + 1) kt [] (by omega) hvt (hTt ht)
  rw [Tree.pops_node (find_l5) hw', l5Evs, splice_straight _ l5Pre_straight, l5_popS]
  refine (spliceS_sameStreams _ (ks' := [px c, ps c, [], pv c, (List.range' (c + 1) m).flatMap fun c =>
    l5Seg (ex c) (es c) (px c) (ps c) (defer c) (da c) (pv c)]) ?_).trans (SameStreams.of_eq ?_)
  · simp only [Tree.popsKids]
    rw [px', ps', pst]
    exact .cons (SameStreams.refl _) (.cons (SameStreams.refl _) (.cons (SameStreams.refl _) (.cons pv'
      (.cons pt .nil))))
  simp only [spliceS, List.headD_cons, List.tail_cons]
  rw [List.range'_succ, List.flatMap_cons, l5Seg]
  have w1 : Dest.words rd σ (.stack [.n 18, .n 19]) = [gen ^ ex c, gen ^ es c] := by
    show [σ (.n 18), σ (.n 19)] = _
    rw [h18, h19]
  have w2 : Dest.words rd σ (.heap (.n 33) 0 24) = defer c := by
    rw [← hdl]; exact l5_words_of_reads σ h33 hdef
  have w3 : Dest.words rd σ (.heap (.n 35) 0 2) = [(da c).1, (da c).2] :=
    l5_words_of_reads σ h35 hda
  rw [w1, w2, w3]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]


/-- **`L5From`, the callees' predicates weakened.** -/
theorem L5From.mono {ex es : ℕ → ℕ} {Pxs Pss Pvs Qxs Qss Qvs : ℕ → Tree → Prop}
    (hx : ∀ c t, Pxs c t → Qxs c t) (hs : ∀ c t, Pss c t → Qss c t) (hv : ∀ c t, Pvs c t → Qvs c t) :
    ∀ m c (t : Tree), L5From ex es Pxs Pss Pvs m c t → L5From ex es Qxs Qss Qvs m c t
  | 0, _, _, h => h.elim
  | m + 1, c, _, ⟨σ, bufs, ks, e, h18, h19, hcl, hK⟩ =>
    ⟨σ, bufs, ks, e, h18, h19, hcl, kidsT_imp hK (.cons (hx c) (.cons (hs c) (.cons (fun _ h => h)
      (.cons (hv c) (.cons (L5From.mono hx hs hv m (c + 1)) .nil)))))⟩

end

/-- **A tree predicate implied on the memories the callee serves**, from validity. -/
theorem _root_.LeanVM.Guest.B1.CompleteAtDTBR.monoM {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B B' : ℕ} {T T' : Reader → Tree → Prop}
    (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hB : B ≤ B')
    (hT : ∀ rd, LowDef k rd → MemL rd Lin → ∀ t rets, t.Valid coreProgram rd args rets → T rd t → T' rd t) :
    CompleteAtDTBR fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hTt⟩ := hr rd hl hm
    ⟨t, ht, hT rd hl (memL_append.mp hm).2 t rets ht.2.1 hTt⟩⟩

/-- **The children loop's honest entries**: child `c`'s `l5Seg`, its claim lists' `px c`, `ps c`, `verify_sub`'s
`pv c`. -/
def l5PopsH (px ps pv : ℕ → List Pop) (s : NodeStatement) (w : NodeWitness) : List Pop :=
  (List.range' 0 w.children.length).flatMap fun c =>
    l5Seg (hEx w c) (hEs w c) (px c) (ps c) (hKid s w c).defer (hKid s w c).da (pv c)

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`MainGoalsRR.l5`**: each child's claim lists by trees of honest shape popping `px c`, `ps c`, its `verify_sub`
call by a tree of `Pvs c` popping `pv c` stream by stream, `q` popping `l5PopsH`. -/
theorem mainGoalsRR_l5 (hbl : bytecode.length = 2 ^ 23) (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    {SB SK : String → ℕ} {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStatics fs SB SK)
    {px ps pv : ℕ → List Pop}
    (hV : VerifySubGoalsTBR fs cert fp seed s w
      (fun rd c t => Pvs c t ∧ SameStreams (t.pops coreProgram rd) (pv c)) Bv)
    (hX : ChildListGoalsTBR fs cert fp seed s w
      (fun rd c t => ccHonest (hKid s w c).ex (hMonoX s w c) t ∧ t.pops coreProgram rd = px c)
      (fun rd c t => ccHonest (hKid s w c).es (hMonoS s w c) t ∧ t.pops coreProgram rd = ps c)
      (fun c => B1.Digest.ccBM fs SB (hMonoX s w c) (hKid s w c).ex)
      (fun c => B1.Digest.ccBM fs SB (hMonoS s w c) (hKid s w c).es))
    (hq : ∀ rd, q.p5 rd = l5PopsH px ps pv s w) : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns [])
      (mainPredsHP fs SB SK Bv Pvs s w q).P5 (mainBsH fs SB SK Bv s w).B5 := by
  intro h0
  have hnc16 := hl.atMostSixteenChildren
  have hk := fun c (hc : c < w.children.length) => kidOk cert hbl hn hl hV.goals
    (((hX c hc).1.toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD)
    (((hX c hc).2.toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD) hc
  refine (mainGoalL5TBR fs cert SB hS.main.st hbl hn hl hV hX h0).with_total.monoM le_rfl
    fun rd _ hM t rets hv ⟨hT, htot⟩ => ⟨⟨L5From.mono (fun _ _ h => h.1) (fun _ _ h => h.1) (fun _ _ h => h.1)
      _ _ t hT, htot⟩, ?_⟩
  rw [hq rd, l5PopsH]
  have hv' : t.Valid coreProgram rd (gen ^ 0 :: [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409,
      (hm fs fp seed s w).a77, (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
      (hm fs fp seed s w).a80,
      (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
      gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
      (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
      (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
      (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400]) rets := by
    rw [pow_zero]; exact hv
  exact l5From_popsS (Cr := hP fs fp seed s w 7) (D := hP fs fp seed s w 4) (nk := w.children.length)
    (defer := fun c => (hKid s w c).defer) (da := fun c => (hKid s w c).da)
    (fun _ _ h => h.2) (fun _ _ h => h.2) (fun _ _ h => h.2) (by omega) rfl rfl rfl
    (fun c hc => ⟨(hk c hc).defer_len, ((hk c hc).mem rd hM).2.2.2.2.2.2, ((hk c hc).mem rd hM).2.2.1,
      ((hk c hc).mem rd hM).2.2.2.1⟩) _ 0 t rets (by omega) hv' hT

/-- **`MainSegs.kids`**, `q` popping `l5PopsH` at the child's slots' pushes and its hints past the advised sizes. -/
theorem mainSegs_kids (hl : GuestLimits s w) {q : MainPops}
    (hq : ∀ rd, q.p5 rd = l5PopsH (fun c => Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (fun c => Hints.childSlotPushes ((sPlan s w).childSlots.getD c []))
      (fun c => (w.children[c]?.map fun ch => (Hints.childHints bytecode seed ch).drop 4).getD []) s w)
    (rd : Reader) :
    SameStreamsBut Hints.heapSizeStream (if (hm fs 0 seed s w).nc = 0 then [] else q.p5 rd)
      (childSeg bytecode seed s w) := by
  have h := l5Segs_honest (bytecode := bytecode) (seed := seed) (s := s) (w := w) (ex := hEx w) (es := hEs w)
    (px := fun c => Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
    (ps := fun c => Hints.childSlotPushes ((sPlan s w).childSlots.getD c []))
    (pv := fun c => (w.children[c]?.map fun ch => (Hints.childHints bytecode seed ch).drop 4).getD [])
    (defer := fun c => (hKid s w c).defer) (da := fun c => (hKid s w c).da) fun c hc => by
      have hmem := List.getElem_mem hc
      have h1 := (hl.childClaimListsBelow2Pow23 _ hmem).1
      have h2 := (hl.childClaimListsBelow2Pow23 _ hmem).2
      refine ⟨?_, ?_, SameStreams.refl _, SameStreams.refl _, hKid_defer hc, by rw [hKid_da hc]; rfl, ?_⟩
      · rw [show hEx w c = (hKid s w c).ex from rfl, hKid_ex hc]; exact gen_pow_count (by omega)
      · rw [show hEs w c = (hKid s w c).es from rfl, hKid_es hc]; exact gen_pow_count (by omega)
      · rw [List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]
        exact SameStreams.refl _
  split
  · next h0 =>
    have : w.children.length = 0 := h0
    rw [this] at h
    exact h
  · rw [hq rd]
    exact h

end
end LeanVM.Guest.B1.Main
