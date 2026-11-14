module

public import LeanVM.Guest.Mode.Jump

/-!
# Calls and returns, in the executor

`call_enter`: a call the walk accepts (`JumpK.call`) enters, in the executor, a callee whose
signature is one of the call's, in a frame the caller's product names (`Frames`), its header naming
the caller's return pc and frame, and the callee's walk starts from a state that holds there, given
the callees' termination facts and the jump table's run. `ret_regs`: a return from a frame whose
header names `r` and `fp` goes there. `ret_resume`: the callee's guarantees at its return give the
state the caller's walk goes on from.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- The program's pcs are small: its signatures' and its jump table's. -/
def EnvSmall (En : Env) : Prop :=
  (∀ t G, En.sigs.get t = some G → t < 2 ^ 62) ∧ ∀ d e, En.jt.get d = some e → e < 2 ^ 62

/-- `mapOpt`'s result, element by element. -/
theorem mapOpt_get {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (acc ys : List β),
      List.rec (motive := fun _ ↦ List β → Option (List β)) (fun acc ↦ some acc.reverse)
        (fun x _ ih acc ↦ match f x with
          | some y => ih (y :: acc)
          | none => none) l acc = some ys →
      ∃ ys', ys = acc.reverse ++ ys' ∧ ∀ i (h : i < l.length), ∃ y, ys'[i]? = some y ∧ f (l[i]'h) = some y
  | [], acc, ys, h => by cases h; exact ⟨[], by simp, fun i h ↦ absurd h (by simp)⟩
  | a :: l, acc, ys, h => by
    simp only at h
    split at h
    · rename_i y hy
      obtain ⟨ys', rfl, hys⟩ := mapOpt_get f l (y :: acc) ys h
      refine ⟨y :: ys', by simp, fun i hi ↦ ?_⟩
      cases i with
      | zero => exact ⟨y, rfl, hy⟩
      | succ i =>
        obtain ⟨z, hz, hfz⟩ := hys i (by simpa using hi)
        exact ⟨z, by simpa using hz, by simpa using hfz⟩
    · cases h

theorem mapOpt_get' {α β : Type} {f : α → Option β} {l : List α} {ys : List β} (h : mapOpt f l = some ys)
    {i : ℕ} (hi : i < l.length) : ∃ y, ys[i]? = some y ∧ f (l[i]'hi) = some y := by
  obtain ⟨ys', hys, h'⟩ := mapOpt_get f l [] ys h
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  exact h' i hi

/-- **The arm a call enters**: its index among the call's signatures, at the pc the executor goes to,
the table's selector having that exponent. -/
theorem callee_at {En : Env} {F : Fun} {i : ℕ} {A : Abs} {d : ℕ} {Gs : List Sig} {s : St} {pc : ℕ}
    (hA : Holds s A) (hE : EnvOk s En) (hS : EnvSmall En) (hc : calleesOf En F A i d = some Gs)
    (hpc : pc < 2 ^ 62) (hv : s.mem.get (s.fp + d) = some (ofK (g ^ pc))) :
    ∃ j G, Gs[j]? = some G ∧ En.sigs.get pc = some G ∧ ∀ x, selOf A d = some x → IdxVal s (.ex x 0) j := by
  unfold calleesOf at hc
  split at hc
  · rename_i e hd
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨u, hu, hok⟩ := hA.v d _ hd
    rw [hv] at hu
    cases hu
    have he := hS.1 e G hG
    obtain rfl := gpow_inj (by omega) (by omega) (ofK_injective (pow_val hok))
    refine ⟨0, G, rfl, hG, fun x hx ↦ ?_⟩
    unfold selOf at hx
    rw [hd] at hx
    cases hx
  · rename_i x d0 htab
    split at hc
    · rename_i n hn
      split_ifs at hc with hcnd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨hlt, hlo⟩, hhi⟩ := hcnd
      obtain ⟨X, hX, hXn⟩ := Abs.ltI_sound hA hlt (show IdxVal s (.num n) n from rfl)
      obtain ⟨vx, ex, hbx, rfl, hex, rfl⟩ := hX
      obtain ⟨u, hu, c, cc, hmc, hnc, hgc⟩ := hA.v d _ htab
      rw [hv] at hu
      cases hu
      obtain ⟨p, hp, rfl⟩ := MonoVal.base1.mp hmc
      obtain rfl := hbx.unique hp
      rw [← ofK_mul, ← pow_add] at hnc
      obtain rfl := names_ofK (by have := hE.2.1; unfold maxCells at this; omega) hnc
      obtain ⟨G, hG, hfy⟩ := mapOpt_get' hc (i := X + 0) (by simp; omega)
      simp only [List.getElem_range] at hfy
      rw [Nat.add_zero] at hfy hG
      obtain ⟨tgt, htgt, hsig⟩ := Option.bind_eq_some_iff.mp hfy
      have hcell := hE.2.2 (d0 + X) tgt (by omega) (by omega) htgt
      rw [hgc] at hcell
      have ht := hS.2 _ _ htgt
      obtain rfl := gpow_inj (by omega) (by omega) (ofK_injective (Option.some.inj hcell))
      refine ⟨X, G, hG, hsig, fun x' hx' ↦ ?_⟩
      unfold selOf at hx'
      rw [htab] at hx'
      cases hx'
      exact ⟨_, X, hbx, rfl, hex, rfl⟩
    · cases hc
  · cases hc

/-- **What holds when a selector's exponent is `j`**: the facts under that condition, and its bounds. -/
theorem Holds.assume {s : St} {A : Abs} (hA : Holds s A) {sel : Option Base} {j : ℕ}
    (hsel : ∀ x, sel = some x → IdxVal s (.ex x 0) j) : Holds s (A.assume sel j) := by
  cases sel with
  | none => exact hA
  | some x =>
    have hi := hsel x rfl
    have h1 := (hA.addLt (a := .ex x 0) (b := .num (j + 1)) ⟨j, j + 1, hi, rfl, by omega⟩).addLt
      (a := .num j) (b := .ex x 1) ⟨j, j + 1, rfl, Idx.succ_val' hi, by omega⟩
    unfold Abs.assume
    dsimp only
    split
    · rename_i c hc
      have hm := List.mem_of_find?_eq_some hc
      have hk := List.find?_some hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨-, hf⟩ := hA.c c hm
      obtain ⟨hh, hr, hp, hlt, hhv⟩ := hf (by rw [Base.beq_eq hk.1, hk.2]; exact hi)
      exact { h1 with
        h := fun k hk' ↦ (List.mem_append.mp hk').elim (hh k) (h1.h k)
        r := fun r hr' ↦ (List.mem_append.mp hr').elim (hr r) (h1.r r)
        p := fun q hq ↦ (List.mem_append.mp hq).elim (hp q) (h1.p q)
        lt := fun q hq ↦ (List.mem_append.mp hq).elim (hlt q) (h1.lt q)
        hv := fun q hq ↦ (List.mem_append.mp hq).elim (h1.hv q) (fun hq ↦ hhv q (List.mem_filter.mp hq).1) }
    · exact h1

/-- The callee a call enters: one of its signatures, at the pc the executor goes to. -/
theorem callee_of {En : Env} {F : Fun} {i : ℕ} {A : Abs} {d : ℕ} {Gs : List Sig} {s : St} {pc : ℕ}
    (hA : Holds s A) (hE : EnvOk s En) (hS : EnvSmall En) (hc : calleesOf En F A i d = some Gs)
    (hpc : pc < 2 ^ 62) (hv : s.mem.get (s.fp + d) = some (ofK (g ^ pc))) :
    ∃ G ∈ Gs, En.sigs.get pc = some G := by
  unfold calleesOf at hc
  split at hc
  · rename_i e hd
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨u, hu, hok⟩ := hA.v d _ hd
    rw [hv] at hu
    cases hu
    have he := hS.1 e G hG
    obtain rfl := gpow_inj (by omega) (by omega) (ofK_injective (pow_val hok))
    exact ⟨G, List.mem_singleton_self _, hG⟩
  · rename_i x d0 htab
    split at hc
    · rename_i n hn
      split_ifs at hc with hcnd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨hlt, hlo⟩, hhi⟩ := hcnd
      obtain ⟨X, hX, hXn⟩ := Abs.ltI_sound hA hlt (show IdxVal s (.num n) n from rfl)
      obtain ⟨vx, ex, hbx, rfl, hex, rfl⟩ := hX
      obtain ⟨u, hu, c, cc, hmc, hnc, hgc⟩ := hA.v d _ htab
      rw [hv] at hu
      cases hu
      obtain ⟨p, hp, rfl⟩ := MonoVal.base1.mp hmc
      obtain rfl := hbx.unique hp
      rw [← ofK_mul, ← pow_add] at hnc
      obtain rfl := names_ofK (by have := hE.2.1; unfold maxCells at this; omega) hnc
      obtain ⟨G, hG, hfy⟩ := mem_mapOpt hc (List.mem_range.mpr (show X + 0 < n by omega))
      rw [Nat.add_zero] at hfy
      obtain ⟨tgt, htgt, hsig⟩ := Option.bind_eq_some_iff.mp hfy
      have hcell := hE.2.2 (d0 + X) tgt (by omega) (by omega) htgt
      rw [hgc] at hcell
      have ht := hS.2 _ _ htgt
      obtain rfl := gpow_inj (by omega) (by omega) (ofK_injective (Option.some.inj hcell))
      exact ⟨G, hG, hsig⟩
    · cases hc
  · cases hc

/-- The caller's state at a callee's: its memory, its frame. -/
def callerAt (sE : St) (fp : ℕ) : St := { sE with fp := fp }

theorem foldl_atCall_sound {sC sE : St} {mq : Mono} (F : Frames sC sE mq) :
    ∀ (Gs : List Sig) {A : Abs}, Holds sC A → (∀ G ∈ Gs, ∀ p ∈ G.term, LTF sE p.1 p.2) →
      Holds sC (foldlA (fun A G ↦ atCall A mq G) A Gs) := by
  intro Gs A hA hT
  rw [foldlA_eq]
  induction Gs generalizing A with
  | nil => exact hA
  | cons G Gs ih =>
    rw [List.foldl_cons]
    exact ih (atCall_sound F hA (hT G (List.mem_cons_self ..)))
      fun G' hG' ↦ hT G' (List.mem_cons_of_mem _ hG')

/-- **A call's entry**: the executor's state `sE` after the call's `JUMP` from `s` is the entry of an
arm `j` of the call's, its frame named by the caller's product, its header naming the caller's
return pc and frame, the table's selector having exponent `j`; its walk's entry state holds there,
and the caller's state for that arm (its facts under the selector, the arm's termination facts)
holds of the caller's frame. -/
theorem call_enter {En : Env} {F : Fun} {i : ℕ} {A : Abs} {d f : ℕ} {mq : Mono} {r : ℕ} {G : Sig}
    {Gs : List Sig} {s sE : St} (hA : Holds s A) (hE : EnvOk s En) (hS : EnvSmall En)
    (hfm : A.mono f = some mq) (h1 : A.hvGet (mq.shift 1) = some (.m ⟨1, 0, []⟩))
    (h0 : A.hvGet (mq.shift 0) = some (.m ⟨0, r, []⟩)) (hc : calleesOf En F A i d = some (G :: Gs))
    (hw : ∀ p ∈ (G :: Gs).zipIdx, entryW (A.assume (selOf A d) p.2) mq p.1 = true)
    (hok : ∀ p ∈ (G :: Gs).zipIdx.map (fun p ↦ (p.1, atCall (A.assume (selOf A d) p.2) mq p.1)),
      entryOk p.2 mq p.1 = true)
    (hfp : s.fp < maxCells) (hle : s.mem ≤ sE.mem) (hwf : sE.mem.WF) (hu : sE.mem.used ≤ maxCells)
    (hfpE : sE.fp < maxCells) (hpcE : sE.pc < 2 ^ 62)
    (hd : s.mem.get (s.fp + d) = some (ofK (g ^ sE.pc)))
    (hf : s.mem.get (s.fp + f) = some (ofK (g ^ sE.fp)))
    (hT : ∀ G', En.sigs.get sE.pc = some G' → (∀ o ∈ G'.entry, sE.mem.written (sE.fp + o) = true) →
      ∀ p ∈ G'.term, LTF sE p.1 p.2) (hjt : RW sE (jtRng En)) :
    Frames (callerAt sE s.fp) sE mq ∧
      sE.mem.get (sE.fp + 1) = some (ofK (g ^ s.fp)) ∧ sE.mem.get (sE.fp + 0) = some (ofK (g ^ r)) ∧
      ∃ j G', (G :: Gs)[j]? = some G' ∧ En.sigs.get sE.pc = some G' ∧
        (∀ x, selOf A d = some x → IdxVal (callerAt sE s.fp) (.ex x 0) j) ∧
        Holds (callerAt sE s.fp) (atCall (A.assume (selOf A d) j) mq G') ∧
        (∀ o ∈ G'.entry, sE.mem.written (sE.fp + o) = true) ∧ Holds sE (entryAbs En G') := by
  have hAC : Holds (callerAt sE s.fp) A := Holds.mono (s' := callerAt sE s.fp) hle rfl hA
  obtain ⟨u, hu, hmu⟩ := hA.mono_val hfm (written_of_get hf)
  rw [hf] at hu
  cases hu
  have Fr : Frames (callerAt sE s.fp) sE mq := ⟨rfl, MonoVal.mono (s' := callerAt sE s.fp) hle rfl hmu, hfpE, hfp, hwf, hu⟩
  obtain ⟨w1, hw1, hm1⟩ := hvGet_cell Fr hAC (by norm_num) h1
  obtain ⟨w0, hw0, hm0⟩ := hvGet_cell Fr hAC (by norm_num) h0
  have e1 : w1 = ofK (g ^ s.fp) := by
    have := pow_val' hm1
    rw [Nat.mul_one, Nat.add_zero] at this
    exact this
  have e0 : w0 = ofK (g ^ r) := pow_val hm0
  obtain ⟨j, G', hj, hsig, hsel⟩ := callee_at hA hE hS hc hpcE hd
  have hsel' : ∀ x, selOf A d = some x → IdxVal (callerAt sE s.fp) (.ex x 0) j :=
    fun x hx ↦ (hsel x hx).mono (s' := callerAt sE s.fp) hle rfl
  have hA0 := hAC.assume hsel'
  have hW := entryW_sound Fr hA0 (hw (G', j) (List.mk_mem_zipIdx_iff_getElem?.mpr hj))
  have hT' := hT G' hsig hW
  have hA1 := atCall_sound Fr hA0 hT'
  have hmem : (G', atCall (A.assume (selOf A d) j) mq G') ∈
      (G :: Gs).zipIdx.map (fun p ↦ (p.1, atCall (A.assume (selOf A d) p.2) mq p.1)) :=
    List.mem_map.mpr ⟨(G', j), List.mk_mem_zipIdx_iff_getElem?.mpr hj, rfl⟩
  exact ⟨Fr, e1 ▸ hw1, e0 ▸ hw0, j, G', hj, hsig, hsel', hA1, hW,
    entryOk_sound Fr hA1 (hok _ hmem) hjt hT'⟩

theorem mem_filter_sub {α : Type} {p : α → Bool} {l : List α} {x : α} (h : x ∈ l.filter p) : x ∈ l :=
  (List.mem_filter.mp h).1

/-- A pointer each of whose cells past it the walk knows is one whose cells are all known. -/
theorem Abs.ptrAt_of_each {A : Abs} {k : Mono} {os : List ℕ} (hne : os ≠ [])
    (h : ∀ t ∈ os, A.ptrAt k [t] = true) : A.ptrAt k os = true := by
  obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil os hne
  have h0 := h t0 ht0
  unfold Abs.ptrAt at h0 ⊢
  split at h0
  · rename_i m hm
    refine List.all_eq_true.mpr fun t ht ↦ ?_
    have := h t ht
    unfold Abs.ptrAt at this
    rw [hm] at this
    simpa using this
  · cases h0

/-- **A pointer every arm knows**: the run of one pointer `armPtrs` keeps holds where an arm does. -/
theorem armPtrs_sound {s : St} {M : Abs} {Bs : List Abs} {X : Abs} (hm : X ∈ Bs) (hX : Holds s X)
    (hfp : s.fp < maxCells) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) {q : Rng × List ℕ}
    (hq : q ∈ armPtrs M Bs) : PW s q.1 q.2 := by
  match Bs, hq with
  | B :: Y :: Ys, hq =>
    unfold armPtrs at hq
    obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp hq
    dsimp only at hp
    split_ifs at hp with h1 h2
    cases hp
    have hall : ∀ t ∈ (List.range 64).filter (fun t ↦ (B :: Y :: Ys).all fun Z ↦ Z.ptrAt p.1 [t]),
        X.ptrAt p.1 [t] = true := fun t ht ↦
      List.all_eq_true.mp (List.mem_filter.mp ht).2 X hm
    have hne : (List.range 64).filter (fun t ↦ (B :: Y :: Ys).all fun Z ↦ Z.ptrAt p.1 [t]) ≠ [] := by
      intro he; rw [he] at h2; exact h2 rfl
    obtain ⟨v, x, hv, hx, hpx⟩ := Abs.ptrAt_sound hX hfp hwf hu (Abs.ptrAt_of_each hne hall)
    refine ⟨v, 0, 1, hv, rfl, rfl, fun j hj1 hj2 ↦ ?_⟩
    obtain rfl : j = 0 := by omega
    refine ⟨x, ?_, hpx⟩
    simpa using hx

/-- **The arms met**: the arm that ran holds, at its index under the selector. -/
theorem armsMeet_sound {s : St} {sel : Option Base} {Bs : List Abs} {j : ℕ} {X : Abs}
    (hj : Bs[j]? = some X) (hX : Holds s X) (hsel : ∀ x, sel = some x → IdxVal s (.ex x 0) j)
    (hfp : s.fp < maxCells) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) :
    Holds s (armsMeet sel Bs) := by
  match Bs, hj with
  | B :: Bs, hj =>
    have hM0 : Holds s (foldlA Abs.interS B Bs) := by
      have e : foldlA Abs.interS B Bs = Bs.foldl Abs.inter B := by
        rw [foldlA_eq]
        exact congrArg (fun f ↦ Bs.foldl f B) (funext fun A ↦ funext fun B ↦ Abs.interS_eq A B)
      rw [e]
      exact Holds.foldl_inter (List.mem_of_getElem? hj) hX
    have hM : Holds s { foldlA Abs.interS B Bs with
        p := armPtrs (foldlA Abs.interS B Bs) (B :: Bs) ++ (foldlA Abs.interS B Bs).p } :=
      { hM0 with
        p := fun q hq ↦ (List.mem_append.mp hq).elim
          (armPtrs_sound (List.mem_of_getElem? hj) hX hfp hwf hu) (hM0.p q) }
    unfold armsMeet
    dsimp only
    split
    · exact hM
    · rename_i x
      have hi := hsel x rfl
      refine { hM with c := fun d hd ↦ ?_ }
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨⟨Y, j'⟩, hY, hd⟩ := List.mem_filterMap.mp hd
        unfold condDiff at hd
        dsimp only at hd
        split_ifs at hd
        cases hd
        obtain ⟨v, e, hv, -, -, -⟩ := id hi
        refine ⟨⟨v, hv⟩, fun hi' ↦ ?_⟩
        have hjj : j' = j := hi'.unique hi
        subst hjj
        have hYX : Y = X := by
          have := List.mk_mem_zipIdx_iff_getElem?.mp hY
          rw [hj] at this
          exact (Option.some.inj this).symm
        subst hYX
        exact ⟨fun k hk ↦ hX.h k (mem_filter_sub hk), fun r hr ↦ hX.r r (mem_filter_sub hr),
          fun q hq ↦ hX.p q (mem_filter_sub hq), fun p hp ↦ hX.lt p (mem_filter_sub hp),
          fun p hp ↦ hX.hv p (mem_filter_sub hp)⟩
      · exact hM.c d (mem_filter_sub hd)

/-- **A return's registers**: a frame whose header names `r` and `fp` returns there. -/
theorem ret_regs {s s' : St} {r fp : ℕ} (hr : r < 2 ^ 62) (hfp : fp < maxCells)
    (h0 : s.mem.get (s.fp + 0) = some (ofK (g ^ r))) (h1 : s.mem.get (s.fp + 1) = some (ofK (g ^ fp)))
    (hpc' : s'.pc < 2 ^ 62) (hfp' : s'.fp < maxCells)
    (hd : s.mem.get (s.fp + 0) = some (ofK (g ^ s'.pc)))
    (hf : s.mem.get (s.fp + 1) = some (ofK (g ^ s'.fp))) : s'.pc = r ∧ s'.fp = fp := by
  rw [h0] at hd
  rw [h1] at hf
  exact ⟨gpow_inj (by omega) (by omega) (ofK_injective (Option.some.inj hd)).symm,
    gpow_inj (by unfold maxCells at hfp'; omega) (by unfold maxCells at hfp; omega)
      (ofK_injective (Option.some.inj hf)).symm⟩

/-- **After a return**: the guarantees of the arm `j` that ran, at its return, give the state the
caller's walk goes on from. -/
theorem ret_resume {sC sR : St} {A : Abs} {sel : Option Base} {mq : Mono} {Gs : List Sig} {j : ℕ}
    {G' : Sig} (hj : Gs[j]? = some G') (F : Frames sC sR mq)
    (hA : Holds sC (atCall (A.assume sel j) mq G')) (hsel : ∀ x, sel = some x → IdxVal sC (.ex x 0) j)
    (hR : RetHolds sR G') (hL : ∀ r ∈ G'.postL, RW sR r) (hLP : ∀ q ∈ G'.postLP, PW sR q.1 q.2)
    (hT : ∀ p ∈ G'.term, LTF sR p.1 p.2) :
    Holds sC (armsMeet sel ((Gs.zipIdx.map fun p ↦ (p.1, atCall (A.assume sel p.2) mq p.1)).map
      fun p ↦ afterCall p.2 mq p.1)) := by
  refine armsMeet_sound (j := j) ?_ (afterCall_sound F hA hR hL hLP hT) hsel F.fpC F.wf F.used
  simp only [List.getElem?_map, List.getElem?_zipIdx, hj, Option.map_some, Nat.zero_add]

end

end LeanVM.Guest.Mode
