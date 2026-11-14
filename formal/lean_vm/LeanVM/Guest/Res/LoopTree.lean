/-
  LeanVM.Guest.Res.LoopTree

  A loop's counter on a valid tree: below its end by the iterations its run still makes, and a power
  of `g` whose exponent and subtree fit the tree.
-/

module

public import LeanVM.Guest.Res.LoopEntry

/-!
# A loop's counter on a valid tree

`chain`: a valid tree of a loop helper of its shape (`loopShape`) at counter `i` reaches its end
after `m` iterations, `i·g^m` the end, `1 ≤ m` at most the tree's words (each iteration a frame of at
least a word): a run stops where its next counter meets its end, its last tail call untaken.

`insts_ctr`: on a valid tree whose functions pass `termChk` (`ProgOk`), every instance of a loop
helper has as counter a power `g^e` with `e` plus its subtree's words at most `B`, given the root's
subtree within `B - 1` words and the root not a loop helper: a loop is entered from outside at `g^0`
or `g^1` (`entL_sound`), and each tail call steps the counter once in a subtree one frame smaller.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A loop helper's end at valuation `σ`: its second parameter, or the constant `g^e`. -/
def endVal (σ : Val) (fn : Fn) : Option ℕ → E
  | some e => ofK (addressOfIndex e)
  | none => match fn.params with
    | _ :: p1 :: _ => σ p1
    | _ => 0

/-- **What the check gives of a program's functions**: a loop helper is named so and has its shape
at an end, its body without the tail passing `entL`; another function's body passes `entL`. -/
structure ProgOk (P : Core.Program) : Prop where
  loop : ∀ f fn, P.find? f = some fn → fn.loop = true →
    isLoopName f = true ∧ ∃ e, endOfFn fn = some e ∧ loopShape fn e = some (loopBody fn) ∧
      entL true [] (loopBody fn) = true
  body : ∀ f fn, P.find? f = some fn → fn.loop = false → entL false [] fn.body = true

theorem ofK_gpow_add (a b : ℕ) :
    ofK (addressOfIndex a) * ofK (addressOfIndex b) = ofK (addressOfIndex (a + b)) := by
  rw [← ofK_mulS, Parameters.addressOfIndex, Parameters.addressOfIndex, Parameters.addressOfIndex, pow_add]

/-- The callees of the frames a list of calls ending with `c` sets up, split. -/
theorem kidsValid_snoc {P : Core.Program} {rd : Reader} {σ : Val} {c : Call} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ (cs ++ [c]) ks →
      ∃ ks' k, ks = ks' ++ [k] ∧ Tree.KidsValid P rd σ cs ks' ∧ k.name = c.f ∧
        (if c.taken then k.Valid P rd (c.args.map σ) (c.rets.map σ)
          else (∃ f σ', k = .phantom f σ') ∧ Phantom P k (c.args.map σ))
  | [], [], h => by simp [Tree.KidsValid] at h
  | [], k :: ks, h => by
    cases ks with
    | nil =>
      simp only [List.nil_append, Tree.KidsValid, and_true] at h
      exact ⟨[], k, rfl, by simp [Tree.KidsValid], h.1, h.2⟩
    | cons _ _ => simp [Tree.KidsValid] at h
  | _ :: _, [], h => by simp [Tree.KidsValid] at h
  | c' :: cs, k :: ks, h => by
    simp only [List.cons_append, Tree.KidsValid] at h
    obtain ⟨ks', k', rfl, h1, h2⟩ := kidsValid_snoc h.2.2
    exact ⟨k :: ks', k', rfl, ⟨h.1, h.2.1, h1⟩, h2⟩

theorem calls_append (es es' : List Ev) : calls (es ++ es') = calls es ++ calls es' := by
  simp [calls, List.filterMap_append]

theorem totalKids_snoc {fs : String → ℕ} (ks : List Tree) (k : Tree) :
    k.total fs ≤ Tree.totalKids fs (ks ++ [k]) := by
  rw [totalKids_eq_sum, List.map_append, List.sum_append]; simp

/-- **A loop helper's path**: its events those of its body without the tail, the tail's guard,
then its tail call, entered unless the next counter meets the end. -/
theorem loop_path {rd : Reader} {σ : Val} {fn : Fn} {e : Option ℕ} (hs : loopShape fn e = some (loopBody fn))
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : HoldsAll rd σ es) :
    ∃ p0 prest c i' es1, fn.params = p0 :: prest ∧ walk σ (loopBody fn) = .fall es1 ∧
      es = es1 ++ [.inK c, if σ c = 0 then .skip fn.name (i' :: prest) else .call fn.name (i' :: prest) []] ∧
      σ i' = σ p0 * ofK (addressOfIndex 1) ∧ σ c = σ p0 * ofK (addressOfIndex 1) + endVal σ fn e := by
  obtain ⟨c, i', p0, prest, hps, hb, hnr, hst, x, y, hd, hxy⟩ := loopShape_spec hs
  rw [hb, walk_append] at hw
  rcases walk_noRet (σ := σ) (loopBody fn) hnr with ⟨es1, h1⟩ | h1
  · rw [h1] at hw
    simp only [walk, walk1, Out.seq, Out.pre, List.append_nil] at hw
    have hes : es = es1 ++ [.inK c, if σ c = 0 then .skip fn.name (i' :: prest) else .call fn.name (i' :: prest) []] := by
      cases hw; simp
    have hh1 : HoldsAll rd σ es1 := fun ev hev ↦ hh ev (by rw [hes]; exact List.mem_append_left _ hev)
    have hi := isStep_val hnr h1 hh1 hst
    have hc : σ c = σ x + σ y := defAtom_holds hnr h1 hh1 hd
    have hend : ∀ z, isEnd (loopBody fn) prest.head? e z = true → σ z = endVal σ fn e := fun z hz ↦ by
      obtain ⟨hn, hs'⟩ := isEnd_val hnr h1 hh1 hz
      cases e with
      | none =>
        have := hn rfl
        simp only [endVal, hps]
        cases prest with
        | nil => cases this
        | cons p1 _ => simp only [List.head?_cons, Option.some.injEq] at this; rw [this]
      | some e => exact hs' e rfl
    refine ⟨p0, prest, c, i', es1, hps, h1, hes, hi, ?_⟩
    rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · rw [hc, isStep_val hnr h1 hh1 hx, hend y hy]
    · rw [hc, isStep_val hnr h1 hh1 hy, hend x hx, add_comm]
  · rw [h1] at hw; simp [Out.seq] at hw

theorem char2_eq {a b : E} (h : a + b = 0) : a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h; exact h

/-- The frames a loop helper's path sets up: those of its body without the tail, then its tail call. -/
theorem loop_calls {σ : Val} {f : String} {c i' : V} {prest : List V} {es1 : List Ev} :
    calls (es1 ++ [.inK c, if σ c = 0 then .skip f (i' :: prest) else .call f (i' :: prest) []]) =
      calls es1 ++ [⟨f, i' :: prest, [], decide (σ c ≠ 0)⟩] := by
  rw [calls_append]
  congr 1
  split_ifs with h <;> simp [calls, List.filterMap_cons, Ev.call?, h]

section

variable {rd : Reader} {fs : String → ℕ} {P : Core.Program}

/-- **A loop's run reaches its end**: a valid tree of a loop helper of its shape at counter `i`
makes `m` iterations, `1 ≤ m` at most its words, `i·g^m` its end. -/
theorem chain (hfs : ∀ f, 1 ≤ fs f) : ∀ (n : ℕ) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    {args rets : List E} {fn : Fn} {e : Option ℕ}, (Memory.Tree.node f σ bufs kids).total fs ≤ n →
    (Memory.Tree.node f σ bufs kids).Valid P rd args rets → P.find? f = some fn →
    loopShape fn e = some (loopBody fn) →
    ∃ m p0 prest, fn.params = p0 :: prest ∧ 1 ≤ m ∧ m ≤ (Memory.Tree.node f σ bufs kids).total fs ∧
      σ p0 * ofK (addressOfIndex m) = endVal σ fn e
  | 0, f, σ, bufs, kids, _, _, _, _, htot, _, _, _ => by
    have := le_total (fs := fs) (Memory.Tree.node f σ bufs kids)
    have := hfs f
    simp only [Tree.name] at *
    omega
  | n + 1, f, σ, bufs, kids, args, rets, fn, e, htot, hv, hf, hs => by
    unfold Tree.Valid at hv
    obtain ⟨fn', hf', -, es, vs, hw, -, hh, hk⟩ := hv
    have hfe := Option.some.inj (hf'.symm.trans hf)
    subst fn'
    obtain ⟨p0, prest, c, i', es1, hps, -, hes, hi, hc⟩ := loop_path hs hw hh
    subst hes
    rw [loop_calls] at hk
    have hname : fn.name = f := fn_name_of_find hf
    have htk : fs f + Tree.totalKids fs kids + bufs.sum = (Memory.Tree.node f σ bufs kids).total fs :=
      (total_node f σ bufs kids).symm
    have h1 := hfs f
    by_cases h0 : σ c = 0
    · refine ⟨1, p0, prest, hps, le_rfl, by omega, ?_⟩
      rw [h0] at hc
      exact char2_eq hc.symm
    · obtain ⟨ks', k, rfl, -, hkn, hkv⟩ := kidsValid_snoc hk
      simp only [ne_eq, h0, not_false_eq_true, decide_true, ↓reduceIte] at hkv hkn
      rcases k with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
      · simp only [Tree.name, hname] at hkn
        subst f'
        have hkt := totalKids_snoc (fs := fs) ks' (Memory.Tree.node f σ' bufs' kids')
        have hkv' := hkv
        unfold Tree.Valid at hkv'
        obtain ⟨fn'', hf'', hpm, -⟩ := hkv'
        have hfe' := Option.some.inj (hf''.symm.trans hf)
        subst fn''
        obtain ⟨m, p0', prest', hps', hm1, hm2, hm⟩ := chain hfs n (by omega) hkv hf hs
        rw [hps] at hps'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
        rw [hps] at hpm
        simp only [List.map_cons, List.cons.injEq] at hpm
        obtain ⟨h0', hrest⟩ := hpm
        have hend : endVal σ' fn e = endVal σ fn e := by
          cases e with
          | some _ => rfl
          | none =>
            simp only [endVal, hps]
            cases prest with
            | nil => rfl
            | cons p1 _ => simp only [List.map_cons, List.cons.injEq] at hrest; exact hrest.1
        refine ⟨m + 1, p0, prest, hps, by omega, by omega, ?_⟩
        rw [← hend, ← hm, h0', hi, mul_assoc, ofK_gpow_add, Nat.add_comm 1 m]
      · exact hkv.elim

/-- **A loop's counter fits**: a power `g^e`, `e` and the subtree's words at most `B`. -/
def CtrOk (P : Core.Program) (fs : String → ℕ) (B : ℕ) (t : Tree) : Prop :=
  ∀ f σ bufs kids fn, t = .node f σ bufs kids → P.find? f = some fn → fn.loop = true →
    ∃ p0 prest e, fn.params = p0 :: prest ∧ σ p0 = ofK (addressOfIndex e) ∧ e + t.total fs ≤ B

/-- A call of a loop helper starts at a power `g^e` with `e + T0 ≤ B + 1`. -/
def CallOk (σ : Val) (B T0 : ℕ) (c : Call) : Prop :=
  isLoopName c.f = true → ∃ a rest e, c.args = a :: rest ∧ σ a = ofK (addressOfIndex e) ∧ e + T0 ≤ B + 1

theorem callOk_start {σ : Val} {B T0 : ℕ} (hT : T0 + 1 ≤ B) {ev : Ev} (h : EntryEv σ ev) {c : Call}
    (hc : ev.call? = some c) : CallOk σ B T0 c := fun hl ↦ by
  obtain ⟨a, rest, ha, hs⟩ := h c hc hl
  rcases hs with hs | hs
  · exact ⟨a, rest, 0, ha, hs, by omega⟩
  · exact ⟨a, rest, 1, ha, hs, by omega⟩

/-- **The calls of a valid node's path start their loops within `B`.** -/
theorem calls_ok (hP : ProgOk P) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {B : ℕ} (hf : P.find? f = some fn) (hC : CtrOk P fs B (.node f σ bufs kids))
    (hB : (Memory.Tree.node f σ bufs kids).total fs + 1 ≤ B) {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) (hh : HoldsAll rd σ es) :
    ∀ c ∈ calls es, CallOk σ B ((Memory.Tree.node f σ bufs kids).total fs) c := by
  cases hl : fn.loop
  · have he := hP.body f fn hf hl
    intro c hc
    obtain ⟨ev, hev, hcv⟩ := List.mem_filterMap.mp hc
    exact callOk_start hB (entL_sound fn.body he (fun _ h ↦ absurd h List.not_mem_nil)
      (by rw [hw]; exact hh) ev (by rw [hw]; exact hev)) hcv
  · obtain ⟨-, e, -, hs, he⟩ := hP.loop f fn hf hl
    obtain ⟨p0, prest, c0, i', es1, hps, hw1, hes, hi, -⟩ := loop_path hs hw hh
    subst hes
    rw [loop_calls]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨ev, hev, hcv⟩ := List.mem_filterMap.mp hc
      exact callOk_start hB (entL_sound (loopBody fn) he (fun _ h ↦ absurd h List.not_mem_nil)
        (by rw [hw1]; exact fun e he' ↦ hh e (List.mem_append_left _ he')) ev (by rw [hw1]; exact hev)) hcv
    · rw [List.mem_singleton] at hc
      subst hc
      intro _
      obtain ⟨p0', prest', e0, hps', h0, he0⟩ := hC f σ bufs kids fn rfl hf hl
      rw [hps] at hps'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
      exact ⟨i', prest, e0 + 1, rfl, by rw [hi, h0, ofK_gpow_add], by omega⟩

theorem kid_total_lt (hfs : ∀ f, 1 ≤ fs f) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {k : Tree}
    (hk : k ∈ kids) : k.total fs + 1 ≤ (Memory.Tree.node f σ bufs kids).total fs := by
  rw [total_node, totalKids_eq_sum]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Tree.total fs) hk)
  have := hfs f
  omega

variable {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **Every loop instance's counter fits**, on a valid tree whose functions pass the check. -/
theorem insts_ctr (hfs : ∀ f, 1 ≤ fs f) (hP : ProgOk P) {B : ℕ} : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E)
    {args rets : List E}, t.Valid P rd args rets → t.total fs + 1 ≤ B → CtrOk P fs B t →
      ∀ J ∈ t.insts fs lp H p hdr, CtrOk P fs B J.t
  | .node f σ bufs kids, p, hdr, args, rets, hv, hB, hC, J, hJ => by
    rw [insts_node, List.mem_cons] at hJ
    rcases hJ with rfl | hJ
    · exact hC
    · have hv' := hv
      unfold Tree.Valid at hv'
      obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv'
      exact instsKids_ctr hfs hP kids σ (calls es) _ 0 _ hk (calls_ok hP hf hC hB hw hh)
        (fun k hk' ↦ kid_total_lt hfs hk') hB J hJ
  | .phantom .., _, _, _, _, hv, _, _, _, _ => hv.elim

theorem instsKids_ctr (hfs : ∀ f, 1 ≤ fs f) (hP : ProgOk P) {B : ℕ} : ∀ (ks : List Tree) (σ : Val)
    (cs : List Call) (I : Inst) (j : ℕ) (ps : List (ℕ × ℕ)) {T0 : ℕ}, Tree.KidsValid P rd σ cs ks →
      (∀ c ∈ cs, CallOk σ B T0 c) → (∀ k ∈ ks, k.total fs + 1 ≤ T0) → T0 + 1 ≤ B →
      ∀ J ∈ Tree.instsKids fs lp H I j ps ks, CtrOk P fs B J.t
  | [], _, _, _, _, _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, _, _, _, _, [], _, _, _, _, _, J, hJ => by
    rw [instsKids_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | k :: ks, σ, c :: cs, I, j, p :: ps, T0, ⟨hn, hc, hks⟩, hcs, hkt, hT, J, hJ => by
    rw [instsKids_cons, List.mem_append] at hJ
    rcases hJ with hJ | hJ
    · cases ht : c.taken
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hc
        rw [insts_phantom, List.mem_singleton] at hJ
        subst hJ
        intro _ _ _ _ _ h; cases h
      · simp only [ht, ↓reduceIte] at hc
        have hk1 := hkt k List.mem_cons_self
        refine insts_ctr hfs hP k p _ hc (by omega) ?_ J hJ
        intro f' σ' bufs' kids' fn' hk' hf' hl
        subst hk'
        have hc' := hc
        unfold Tree.Valid at hc'
        obtain ⟨fn'', hf'', hpm, -⟩ := hc'
        have hfe := Option.some.inj (hf''.symm.trans hf')
        subst fn''
        obtain ⟨hln, _, -, hs, -⟩ := hP.loop f' fn' hf' hl
        obtain ⟨-, -, p0, prest, hps, -⟩ := loopShape_spec hs
        simp only [Tree.name] at hn
        subst f'
        obtain ⟨a, rest, e, ha, hσa, he⟩ := hcs c List.mem_cons_self hln
        rw [hps, ha] at hpm
        simp only [List.map_cons, List.cons.injEq] at hpm
        exact ⟨p0, prest, e, hps, hpm.1.trans hσa, by omega⟩
    · exact instsKids_ctr hfs hP ks σ cs I (j + 1) ps hks (fun c' h ↦ hcs c' (List.mem_cons_of_mem _ h))
        (fun k' h ↦ hkt k' (List.mem_cons_of_mem _ h)) hT J hJ
  | _ :: _, _, [], _, _, _ :: _, _, h, _, _, _, _, _ => h.elim
end

end

end

end LeanVM.Guest.Res
