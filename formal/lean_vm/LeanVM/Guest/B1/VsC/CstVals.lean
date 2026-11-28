/-
  LeanVM.Guest.B1.VsC.CstVals

  `check_stack_terminal`'s calls' words and its allocations on the forward valuation, from the
  body's equations and its arguments alone.
-/

module

public import LeanVM.Guest.B1.VsC.CstOk

/-!
# `check_stack_terminal`'s calls' words

`CstG`: a valuation satisfying the body's equations (`Good`), its buffers at the cursor `c`, its
parameters `StackCtxAt`'s. No word of the node's own buffers or of its callees is needed, so the
valuation fixed before the memory (`σ0`, on a memory where `StackCtxAt` holds) is one.
`CstG.calls`: the calls after the dispatch take the words `cstCallsV` (arguments, buffers, the
tables' heights, the oracle's returns); `CstG.v42`: the dispatch's word; `CstG.v30`: `rchi`'s size.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **What the calls' words need**: the body's equations, the buffers at `c`, the parameters. -/
structure CstG (rd : Reader) (w : ℕ → E) (σ : Val) (layout : Layout) (link : LinkEnd)
    (chi r qPoint kOut kIn f g x z : List E) (rho lam rm : E) (outputs : List ColumnClaim) (c : ℕ) : Prop where
  good : ∀ a ∈ cstAtomsB, Good rd cstS w σ a
  buf : ∀ i < 10, σ (.n (31 + i)) = ptrAtV (cstBase chi.length c i)
  ctx : StackCtxAt rd (cstValArgs σ) layout link chi r qPoint kOut kIn f g x z rho lam rm outputs
  hL : layout.stackLog ≤ 30

/-- The calls' words after the dispatch, in order: arguments, returns. -/
def cstCallsV (args : List E) (layout : Layout) (n c : ℕ) (w : ℕ → E) : List (List E × List E) :=
  [([args.getD 10 0 * gen ^ 39, args.getD 18 0, gen ^ (hgt layout 5 + 6), args.getD 12 0], [w 59]),
    ([ptrAtV (cstBase n c 0), args.getD 5 0, args.getD 18 0, args.getD 12 0, args.getD 6 0], []),
    ([ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 0), ptrAtV (cstBase n c 2), ptrAtV (cstBase n c 1)], [w 471]),
    ([ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 1), ptrAtV (cstBase n c 2) * gen ^ 5,
      ptrAtV (cstBase n c 1) * gen ^ 5], [w 488]),
    ([ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 2), ptrAtV (cstBase n c 2) * gen ^ 10,
      ptrAtV (cstBase n c 1) * gen ^ 10], [w 504]),
    ([ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 3), ptrAtV (cstBase n c 2) * gen ^ 13,
      ptrAtV (cstBase n c 1) * gen ^ 13], [w 522]),
    ([ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 4), ptrAtV (cstBase n c 2) * gen ^ 18,
      ptrAtV (cstBase n c 1) * gen ^ 18], [w 540]),
    ([ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 5), ptrAtV (cstBase n c 2) * gen ^ 23,
      ptrAtV (cstBase n c 1) * gen ^ 23], [w 569]),
    ([ptrAtV (cstBase n c 5), 1, args.getD 7 0, args.getD 18 0, args.getD 8 0], []),
    ([ptrAtV (cstBase n c 6), 1, ptrAtV (cstBase n c 7), args.getD 18 0, args.getD 8 0], []),
    ([ptrAtV (cstBase n c 4), 1, args.getD 10 0, args.getD 18 0, gen ^ (hgt layout 5 + 6)], []),
    ([ptrAtV (cstBase n c 9), 1, args.getD 22 0, args.getD 18 0, args.getD 4 0], []),
    ([ptrAtV (cstBase n c 3), 1, args.getD 5 0, args.getD 18 0, args.getD 6 0], [])]

/-- The header's atoms the allocation's size and the dispatch's word come from. -/
def cstNeedH : List Atom :=
  [.const (.n 23) (word 2 0), .mul (.n 24) (.n 6) (.n 23), .mul (.n 25) (.n 24) (.n 24), .mul (.n 26) (.n 25) (.n 25),
    .mul (.n 27) (.n 26) (.n 26), .mul (.n 28) (.n 27) (.n 27), .mul (.n 29) (.n 28) (.n 28),
    .mul (.n 30) (.n 29) (.n 29)]

set_option maxRecDepth 100000 in
theorem cstNeedH_ok : cstNeedH.all (fun a => decide (a ∈ cstAtomsB)) = true := by decide +kernel

/-- An atom before the assertion that is not a load holds by its equation. -/
theorem good_holds {rd : Reader} {w : ℕ → E} {σ : Val} {a : Atom} (hg : Good rd cstS w σ a) (ha : a ∈ cstAtomsB)
    (hnl : ∀ d p o, a ≠ .load d p o) : a.Holds rd σ := by
  have hA := cst_atomB ha
  cases a with
  | load d p o => exact absurd rfl (hnl d p o)
  | _ => simp only [cstAtomB, Bool.not_eq_true'] at hA; exact holds_noSide hg hA

theorem memRing_tab0 {s : Stmt} (h : s ∈ cstTab0) : s ∈ cstRing := by
  unfold cstRing
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))

theorem memRing_tab : ∀ (t : ℕ) {s : Stmt}, s ∈ (match t with
    | 1 => cstTab 472 5 [18, 17, 14, 15, 16] 47 (word 32 0) 33 32 471 "ring_cols__L5"
    | 2 => cstTab 490 10 [23, 22, 21] 48 (word 32 0) 485 487 489 "ring_cols__L3"
    | 3 => cstTab 506 13 [33, 32, 29, 30, 31] 49 (word 8192 0) 33 32 505 "ring_cols__L5"
    | 4 => cstTab 524 18 [47, 46, 43, 44, 45] 50 (word 32 0) 519 521 523 "ring_cols__L5"
    | _ => cstTab 542 23 [51, 50, 110, 111, 112, 113, 114, 115, 48, 49] 51 (word 32 0) 537 539 541
      "ring_cols__L10") → s ∈ cstRing
  | 1, _, h => by
    unfold cstRing
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
  | 2, _, h => by
    unfold cstRing
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h))))
  | 3, _, h => by
    unfold cstRing
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h)))
  | 4, _, h => by
    unfold cstRing
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  | 0, _, h | _ + 5, _, h => by
    unfold cstRing
    exact List.mem_append_left _ (List.mem_append_right _ h)

theorem cstSq_atoms {w kb : ℕ} {a : Atom} (ha : Stmt.atom a ∈ cstSq w kb) : ∃ d x y, a = .mul d x y := by
  simp only [cstSq, List.mem_cons, List.mem_map, List.mem_range] at ha
  rcases ha with h | ⟨i, -, h⟩
  · exact ⟨_, _, _, Stmt.atom.inj h⟩
  · exact ⟨_, _, _, (Stmt.atom.inj h).symm⟩

theorem cstSq_aoc {w kb : ℕ} : ∀ s ∈ cstSq w kb, atomOrCall s = true := by
  intro s hs
  simp only [cstSq, List.mem_cons, List.mem_map, List.mem_range] at hs
  rcases hs with rfl | ⟨i, -, rfl⟩ <;> rfl

theorem sq_of {rd : Reader} {σ : Val} {w kb : ℕ}
    (hh : ∀ a, Stmt.atom a ∈ cstSq w kb → (∀ d p o, a ≠ .load d p o) → a.Holds rd σ) :
    σ (.n (w + 5)) = σ (.n kb) ^ 64 :=
  sq_facts (C := trivC) (allOk_of_aoc cstSq_aoc (fun a ha => by
    obtain ⟨d, x, y, rfl⟩ := cstSq_atoms ha
    exact hh _ ha fun _ _ _ h => by cases h) fun _ _ _ _ => trivial)

/-- A later table's arguments, from the table's atoms that are not loads. -/
theorem tab_args' {rd : Reader} {σ : Val} {v0 q0 kb rq pm acc : ℕ} {ks : List ℕ} {W : E} {name : String}
    (hh : ∀ a, Stmt.atom a ∈ cstTab v0 q0 ks kb W rq pm acc name → (∀ d p o, a ≠ .load d p o) → a.Holds rd σ) :
    σ (.n (v0 + masksVals ks + 6)) = σ (.n 31) * σ (.n kb) ^ 64 ∧
      σ (.n (v0 + masksVals ks + 8)) = σ (.n rq) * W ∧ σ (.n (v0 + masksVals ks + 10)) = σ (.n pm) * W := by
  have hm : ∀ s ∈ cstSq (v0 + masksVals ks) kb ++
      [osMul (v0 + masksVals ks + 6) 31 (v0 + masksVals ks + 5), osCst (v0 + masksVals ks + 7) W,
        osMul (v0 + masksVals ks + 8) rq (v0 + masksVals ks + 7), osCst (v0 + masksVals ks + 9) W,
        osMul (v0 + masksVals ks + 10) pm (v0 + masksVals ks + 9)], s ∈ cstTab v0 q0 ks kb W rq pm acc name := by
    intro s hs
    unfold cstTab
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
    tauto
  have h5 : σ (.n (v0 + masksVals ks + 5)) = σ (.n kb) ^ 64 :=
    sq_of fun a ha hl => hh a (hm _ (List.mem_append_left _ ha)) hl
  have g : ∀ a, Stmt.atom a ∈ [osMul (v0 + masksVals ks + 6) 31 (v0 + masksVals ks + 5),
      osCst (v0 + masksVals ks + 7) W, osMul (v0 + masksVals ks + 8) rq (v0 + masksVals ks + 7),
      osCst (v0 + masksVals ks + 9) W, osMul (v0 + masksVals ks + 10) pm (v0 + masksVals ks + 9)] →
      (∀ d p o, a ≠ .load d p o) → a.Holds rd σ := fun a ha hl => hh a (hm _ (List.mem_append_right _ ha)) hl
  have h6 : σ (.n (v0 + masksVals ks + 6)) = σ (.n 31) * σ (.n (v0 + masksVals ks + 5)) :=
    g (.mul (.n (v0 + masksVals ks + 6)) (.n 31) (.n (v0 + masksVals ks + 5))) (by simp) (fun _ _ _ h => by cases h)
  have h7 : σ (.n (v0 + masksVals ks + 7)) = W :=
    g (.const (.n (v0 + masksVals ks + 7)) W) (by simp) (fun _ _ _ h => by cases h)
  have h8 : σ (.n (v0 + masksVals ks + 8)) = σ (.n rq) * σ (.n (v0 + masksVals ks + 7)) :=
    g (.mul (.n (v0 + masksVals ks + 8)) (.n rq) (.n (v0 + masksVals ks + 7))) (by simp) (fun _ _ _ h => by cases h)
  have h9 : σ (.n (v0 + masksVals ks + 9)) = W :=
    g (.const (.n (v0 + masksVals ks + 9)) W) (by simp) (fun _ _ _ h => by cases h)
  have h10 : σ (.n (v0 + masksVals ks + 10)) = σ (.n pm) * σ (.n (v0 + masksVals ks + 9)) :=
    g (.mul (.n (v0 + masksVals ks + 10)) (.n pm) (.n (v0 + masksVals ks + 9))) (by simp) (fun _ _ _ h => by cases h)
  rw [h7] at h8
  rw [h9] at h10
  exact ⟨by rw [h6, h5], h8, h10⟩

section
variable {rd : Reader} {w : ℕ → E} {σ : Val} {layout : Layout} {link : LinkEnd}
  {chi r qPoint kOut kIn f g x z : List E} {rho lam rm : E} {outputs : List ColumnClaim} {c : ℕ}
variable (h : CstG rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c)
include h

theorem CstG.nl {a : Atom} (ha : Stmt.atom a ∈ cstBodyB ++ cstTail0) (hnl : ∀ d p o, a ≠ .load d p o) :
    a.Holds rd σ :=
  good_holds (h.good a (mem_atomsB ha)) (mem_atomsB ha) hnl

theorem CstG.kbv : ∀ t < 6, σ (.n (46 + t)) = gen ^ hgt layout t := by
  obtain ⟨-, -, hkb, -⟩ := h.ctx
  intro t ht
  have hm : Atom.load (.n (46 + t)) (.n 1) (2 + t) ∈ cstAtomsB := by
    apply mem_atomsB; apply memB_head; interval_cases t <;> simp [cstHead]
  have hS := cst_fresh_of hm (by omega)
  have hv := kappaSources_get hkb (2 + t) (by omega)
  rw [good_load_eq hv (h.good _ hm) hS]
  have h1 : 2 + t ≠ 1 := by omega
  simp [kvOf, hgt, h1]

theorem CstG.need : ∀ a ∈ cstNeed, a.Holds rd σ := fun a ha => by
  have hm : a ∈ cstAtomsB := by simpa using List.all_eq_true.mp cstNeed_ok a ha
  refine good_holds (h.good a hm) hm fun d p o he => ?_
  subst he
  simp [cstNeed] at ha

theorem CstG.needH : ∀ a ∈ cstNeedH, a.Holds rd σ := fun a ha => by
  have hm : a ∈ cstAtomsB := by simpa using List.all_eq_true.mp cstNeedH_ok a ha
  refine good_holds (h.good a hm) hm fun d p o he => ?_
  subst he
  simp [cstNeedH] at ha

/-- `rchi`'s size word. -/
theorem CstG.v30 : σ (.n 30) = gen ^ (64 * (chi.length + 1)) := by
  obtain ⟨-, -, -, -, -, hgn, -⟩ := h.ctx
  have hN := h.needH
  simp only [cstNeedH, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds, forall_eq] at hN
  obtain ⟨e23, e24, e25, e26, e27, e28, e29, e30⟩ := hN
  have hg : word 2 0 = gen := by
    have := word_two_pow (a := 1) (by norm_num)
    norm_num at this
    exact this
  rw [e30, e29, e28, e27, e26, e25, e24, e23, hgn, hg]
  ring

/-- The dispatch's word. -/
theorem CstG.v42 : σ (.n 42) = ofK (addressOfIndex (layout.stackLog - 16)) := by
  obtain ⟨⟨bytecode, rows, hbl⟩, -, -, hplaced, -⟩ := h.ctx
  have h16 : 16 ≤ layout.stackLog := by rw [(cs_layout hbl h.hL).2.1]; exact le_max_left _ _
  have hN := h.need
  simp only [cstNeed, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds, forall_eq] at hN
  obtain ⟨e41, e42, -⟩ := hN
  rw [e42, e41, hplaced.1, ← gen_pow_eq_ofK]
  calc gen ^ layout.stackLog * word 8198521646651277316 0 =
      gen ^ (layout.stackLog - 16) * (gen ^ 16 * word 8198521646651277316 0) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h16]
    _ = gen ^ (layout.stackLog - 16) := by rw [gen16_inv, mul_one]

/-- **The calls' words after the dispatch.** -/
theorem CstG.calls (hret : ∀ v ∈ [59, 471, 488, 504, 522, 540, 569], σ (.n v) = w v) :
    cstRestCalls.map (fun cl => (cl.args.map σ, cl.rets.map σ)) =
      cstCallsV (cstValArgs σ) layout chi.length c w := by
  have hN := h.need
  simp only [cstNeed, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds, forall_eq] at hN
  obtain ⟨-, -, e55, e56, e57, e58, e572, e609, e612, e613, e614, e615, e616⟩ := hN
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret
  obtain ⟨r59, r471, r488, r504, r522, r540, r569⟩ := hret
  have hh : ∀ a, Stmt.atom a ∈ cstRing → (∀ d p o, a ≠ .load d p o) → a.Holds rd σ :=
    fun a ha hl => h.nl (memB_ring ha) hl
  have a0 : σ (.n 470) = σ (.n 31) * σ (.n 46) ^ 64 := by
    have h5 : σ (.n (464 + 5)) = σ (.n 46) ^ 64 := sq_of fun a ha hl => hh a (memRing_tab0 (by
      unfold cstTab0; exact List.mem_append_left _ (List.mem_append_right _ ha))) hl
    have h6 : σ (.n 470) = σ (.n 31) * σ (.n 469) :=
      hh (.mul (.n 470) (.n 31) (.n 469)) (memRing_tab0 (by unfold cstTab0; simp)) (fun _ _ _ h => by cases h)
    rw [h6]
    exact congrArg _ h5
  have tab : ∀ {v0 q0 kb rq pm acc : ℕ} {ks : List ℕ} {W : E} {name : String},
      (∀ s ∈ cstTab v0 q0 ks kb W rq pm acc name, s ∈ cstRing) →
      σ (.n (v0 + masksVals ks + 6)) = σ (.n 31) * σ (.n kb) ^ 64 ∧
        σ (.n (v0 + masksVals ks + 8)) = σ (.n rq) * W ∧ σ (.n (v0 + masksVals ks + 10)) = σ (.n pm) * W :=
    fun hsub => tab_args' fun a ha hl => hh a (hsub _ ha) hl
  have a1 : σ (.n 483) = σ (.n 31) * σ (.n 47) ^ 64 ∧ σ (.n 485) = σ (.n 33) * word 32 0 ∧
      σ (.n 487) = σ (.n 32) * word 32 0 := tab (fun s hs => memRing_tab 1 hs)
  have a2 : σ (.n 499) = σ (.n 31) * σ (.n 48) ^ 64 ∧ σ (.n 501) = σ (.n 485) * word 32 0 ∧
      σ (.n 503) = σ (.n 487) * word 32 0 := tab (fun s hs => memRing_tab 2 hs)
  have a3 : σ (.n 517) = σ (.n 31) * σ (.n 49) ^ 64 ∧ σ (.n 519) = σ (.n 33) * word 8192 0 ∧
      σ (.n 521) = σ (.n 32) * word 8192 0 := tab (fun s hs => memRing_tab 3 hs)
  have a4 : σ (.n 535) = σ (.n 31) * σ (.n 50) ^ 64 ∧ σ (.n 537) = σ (.n 519) * word 32 0 ∧
      σ (.n 539) = σ (.n 521) * word 32 0 := tab (fun s hs => memRing_tab 4 hs)
  have a5 : σ (.n 564) = σ (.n 31) * σ (.n 51) ^ 64 ∧ σ (.n 566) = σ (.n 537) * word 32 0 ∧
      σ (.n 568) = σ (.n 539) * word 32 0 := tab (fun s hs => memRing_tab 5 hs)
  have k46 : σ (.n 46) = gen ^ hgt layout 0 := h.kbv 0 (by norm_num)
  have k47 : σ (.n 47) = gen ^ hgt layout 1 := h.kbv 1 (by norm_num)
  have k48 : σ (.n 48) = gen ^ hgt layout 2 := h.kbv 2 (by norm_num)
  have k49 : σ (.n 49) = gen ^ hgt layout 3 := h.kbv 3 (by norm_num)
  have k50 : σ (.n 50) = gen ^ hgt layout 4 := h.kbv 4 (by norm_num)
  have k51 : σ (.n 51) = gen ^ hgt layout 5 := h.kbv 5 (by norm_num)
  have b : ∀ i < 10, σ (.n (31 + i)) = ptrAtV (cstBase chi.length c i) := h.buf
  have b31 : σ (.n 31) = ptrAtV (cstBase chi.length c 0) := b 0 (by norm_num)
  have b32 : σ (.n 32) = ptrAtV (cstBase chi.length c 1) := b 1 (by norm_num)
  have b33 : σ (.n 33) = ptrAtV (cstBase chi.length c 2) := b 2 (by norm_num)
  have rowE : ∀ t (kb : ℕ), σ (.n kb) = gen ^ hgt layout t →
      σ (.n 31) * σ (.n kb) ^ 64 = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout t) := fun t kb hk => by
    rw [hk, b31, ← pow_mul, Nat.mul_comm]
  have w5 : word 32 0 = gen ^ 5 := word_g5
  have w13 : word 8192 0 = gen ^ 13 := word_g13
  have f470 : σ (.n 470) = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout 0) := by rw [a0, rowE 0 46 k46]
  have f483 : σ (.n 483) = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout 1) := by rw [a1.1, rowE 1 47 k47]
  have f485 : σ (.n 485) = ptrAtV (cstBase chi.length c 2) * gen ^ 5 := by rw [a1.2.1, w5, b33]
  have f487 : σ (.n 487) = ptrAtV (cstBase chi.length c 1) * gen ^ 5 := by rw [a1.2.2, w5, b32]
  have f499 : σ (.n 499) = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout 2) := by rw [a2.1, rowE 2 48 k48]
  have f501 : σ (.n 501) = ptrAtV (cstBase chi.length c 2) * gen ^ 10 := by
    rw [a2.2.1, f485, w5, mul_assoc, ← pow_add]
  have f503 : σ (.n 503) = ptrAtV (cstBase chi.length c 1) * gen ^ 10 := by
    rw [a2.2.2, f487, w5, mul_assoc, ← pow_add]
  have f517 : σ (.n 517) = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout 3) := by rw [a3.1, rowE 3 49 k49]
  have f519 : σ (.n 519) = ptrAtV (cstBase chi.length c 2) * gen ^ 13 := by rw [a3.2.1, w13, b33]
  have f521 : σ (.n 521) = ptrAtV (cstBase chi.length c 1) * gen ^ 13 := by rw [a3.2.2, w13, b32]
  have f535 : σ (.n 535) = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout 4) := by rw [a4.1, rowE 4 50 k50]
  have f537 : σ (.n 537) = ptrAtV (cstBase chi.length c 2) * gen ^ 18 := by
    rw [a4.2.1, f519, w5, mul_assoc, ← pow_add]
  have f539 : σ (.n 539) = ptrAtV (cstBase chi.length c 1) * gen ^ 18 := by
    rw [a4.2.2, f521, w5, mul_assoc, ← pow_add]
  have f564 : σ (.n 564) = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout 5) := by rw [a5.1, rowE 5 51 k51]
  have f566 : σ (.n 566) = ptrAtV (cstBase chi.length c 2) * gen ^ 23 := by
    rw [a5.2.1, f537, w5, mul_assoc, ← pow_add]
  have f568 : σ (.n 568) = ptrAtV (cstBase chi.length c 1) * gen ^ 23 := by
    rw [a5.2.2, f539, w5, mul_assoc, ← pow_add]
  have f56 : σ (.n 56) = σ (.n 10) * gen ^ 39 := by rw [e56, e55, word_g39]
  have f58 : σ (.n 58) = gen ^ (hgt layout 5 + 6) := by rw [e58, e57, k51, word_g6, ← pow_add]
  have f614 : σ (.n 614) = gen ^ (hgt layout 5 + 6) := by rw [e614, e613, k51, word_g6, ← pow_add]
  have f572 : σ (.n 572) = 1 := by rw [e572, word_one]
  have f609 : σ (.n 609) = 1 := by rw [e609, word_one]
  have f612 : σ (.n 612) = 1 := by rw [e612, word_one]
  have f615 : σ (.n 615) = 1 := by rw [e615, word_one]
  have f616 : σ (.n 616) = 1 := by rw [e616, word_one]
  have b34 : σ (.n 34) = ptrAtV (cstBase chi.length c 3) := b 3 (by norm_num)
  have b35 : σ (.n 35) = ptrAtV (cstBase chi.length c 4) := b 4 (by norm_num)
  have b36 : σ (.n 36) = ptrAtV (cstBase chi.length c 5) := b 5 (by norm_num)
  have b37 : σ (.n 37) = ptrAtV (cstBase chi.length c 6) := b 6 (by norm_num)
  have b38 : σ (.n 38) = ptrAtV (cstBase chi.length c 7) := b 7 (by norm_num)
  have b40 : σ (.n 40) = ptrAtV (cstBase chi.length c 9) := b 9 (by norm_num)
  simp only [cstRestCalls, cstCallsV, List.map_cons, List.map_nil, cstValArgs, List.getD_cons_succ,
    List.getD_cons_zero, f56, f58, r59, b31, b32, b33, b34, b35, b36, b37, b38, b40, f470, f483, f485, f487, f499, f501,
    f503, f517, f519, f521, f535, f537, f539, f564, f566, f568, r471, r488, r504, r522, r540, r569, f572, f609, f612,
    f614, f615, f616]

end

end
end LeanVM.Guest.B1.VsC
