/-
  LeanVM.Guest.B1.Eq.RsWords

  `rs_eq_run`'s words, by hand (it has no words certificate: its dispatch): on `count < 64`
  coordinates, its frame, its chain, `rs_eq_run_loop0`'s `count / 8` iterations (or its tail when
  it is skipped) and the remainder's `rs_eq_rows__L{count % 8}`.
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«rs_eq_run»
import LeanVM.Guest.Value.FieldBits

/-!
# `rs_eq_run` within its words

On a valid tree of `rs_eq_run` at arguments whose count (argument `2`) is `g^c`, `c < 64`
(`TotalLeOn`): its body is flat (`rsBody = rsPre0 ++ rsD :: [copy, ret]`), so its walk's events are
its statements' (the dispatch `rsD` names a callee: else the walk is stuck, `rs_walk_stuck`) and its
frames are `rs_eq_run_loop0`'s and the remainder's `rs_eq_rows__L{r}` (`rs_calls`). Its atoms
`rsA` hold, so `q_g = g^q`, `r_g = g^r` and `g^(8q + r) = count_g = g^c` (`rsA_vals`): `q = c / 8`,
`r = c % 8`; `rsAlloc` and `rsG` hold, so its one `HeapBuf`, the chain, is `64 (q + 2)` words
(`rsAllocG_vals`). With `rs_eq_run_loop0`'s run's words (`TotalLeOn … LoopPre`: `K6` per iteration
and its phantom), each `rs_eq_rows__L{r}`, `r < 8`, within `R`, and a skipped loop's tail within its
frame (`htl`), `rs_totalLeOn` bounds the tree by `fs "rs_eq_run" + (fs "rs_eq_run_loop0" + c / 8 ·
K6) + R + 64 (c / 8 + 2)`; `rs_totalLeOn34`, for `c ≤ 34`, by `fs "rs_eq_run" + (fs
"rs_eq_run_loop0" + 4 · K6) + R + 384`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_run`'s statements before its `ret`. -/
def rsPre : List Stmt := rsA ++ (rsAlloc ++ (rsInits ++ rsT))

/-- Its statements before the remainder's dispatch. -/
def rsPre0 : List Stmt := rsA ++ (rsAlloc ++ (rsInits ++ (rsG ++ rsT0)))

theorem rsBody_split : rsBody = rsPre ++ [.ret [.n (val% «rs_eq_run» "s12#0")]] := by
  simp only [rsBody, rsPre, List.append_assoc]

theorem rsPre_eq : rsPre = rsPre0 ++ [rsD, .atom (.copy (.n (val% «rs_eq_run» "s12#0")) (.n (val% «rs_eq_run» "last")))] := by
  simp only [rsPre, rsPre0, rsT, List.append_assoc]

theorem rsBody_split' : rsBody = rsPre0 ++ (rsD :: [.atom (.copy (.n (val% «rs_eq_run» "s12#0")) (.n (val% «rs_eq_run» "last"))), .ret [.n (val% «rs_eq_run» "s12#0")]]) := by
  rw [rsBody_split, rsPre_eq, List.append_assoc]
  rfl

theorem rs_flat : rsPre.all Stmt.flat = true := by decide +kernel

theorem rsA_atoms : rsA.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem rs_noDispB : rsPre0.all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem rs_dispOk0 (σ : Val) : ∀ s ∈ rsPre0, DispOk σ s := fun s hs ↦ by
  have := List.all_eq_true.mp rs_noDispB s hs
  cases s <;> simp_all [DispOk]

theorem rs_dispOk {σ : Val} (h : ∃ j < 8, σ (.n (val% «rs_eq_run» "r_g@3")) = ofK (addressOfIndex j)) :
    ∀ s ∈ rsPre, DispOk σ s := by
  intro s hs
  rw [rsPre_eq] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hs | rfl | rfl
  · exact rs_dispOk0 σ s hs
  · obtain ⟨j, hj, hx⟩ := h
    exact ⟨j, by simpa using hj, by omega, hx⟩
  · trivial

/-- The fused dispatch names no callee: stuck. -/
theorem pick_stuck (σ : Val) (x : V) (args rets : List V) : ∀ (fs : List String) (j : ℕ),
    (∀ i < fs.length, σ x ≠ ofK (addressOfIndex (j + i))) → pick σ x args rets j fs = .stuck
  | [], _, _ => rfl
  | f :: fs, j, h => by
    unfold pick
    rw [ite_neg' (by simpa using h 0 (by simp))]
    exact pick_stuck σ x args rets fs (j + 1) fun i hi ↦ by
      rw [show j + 1 + i = j + (i + 1) by omega]
      exact h (i + 1) (by simp only [List.length_cons]; omega)

/-- A flat block before a stuck rest: stuck. -/
theorem walk_flat_stuck (σ : Val) : ∀ (pre rest : List Stmt), pre.all Stmt.flat = true →
    (∀ s ∈ pre, DispOk σ s) → walk σ rest = .stuck → walk σ (pre ++ rest) = .stuck
  | [], _, _, _, h => h
  | s :: pre, rest, h, hd, hr => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_flat_stuck σ pre rest h.2 (fun s' hs' ↦ hd s' (by simp [hs']))
      hr, walk1_flat σ s h.1 (hd s (by simp))]
    rfl

/-- **The walk is stuck unless the remainder's selector names a callee.** -/
theorem rs_walk_stuck (σ : Val) (h : ¬ ∃ j < 8, σ (.n (val% «rs_eq_run» "r_g@3")) = ofK (addressOfIndex j)) :
    walk σ (Fn.body fn% «rs_eq_run») = .stuck := by
  rw [rs_eq_run_body, rsBody_split']
  refine walk_flat_stuck σ _ _ (by decide +kernel) (rs_dispOk0 σ) ?_
  rw [walk, rsD, walk1, pick_stuck σ _ _ _ _ 0 fun i hi hx ↦ h ⟨i, by simpa using hi, by
    rwa [Nat.zero_add] at hx⟩]
  rfl

theorem rs_callSF (σ : Val) : rsPre.filterMap (Stmt.callSF σ) =
    [(some (.n (val% «rs_eq_run» "s8#1")), name% «rs_eq_run_loop0», [.n (val% «rs_eq_run» "s8#2"), .n (val% «rs_eq_run» "q_g@3"), .n (val% «rs_eq_run» "chain"), .n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1")], []),
      (none, ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
        "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD
          (logG (σ (.n (val% «rs_eq_run» "r_g@3")))) "", [.n (val% «rs_eq_run» "row"), .n (val% «rs_eq_run» "last~1"), .n (val% «rs_eq_run» "last~2")], [.n (val% «rs_eq_run» "last")])] := rfl

theorem rs_allocSz : rsPre.filterMap Main.Stmt.allocSz =
    [(.n (val% «rs_eq_run» "chain"), .inr (.n (val% «rs_eq_run» "chain~7")))] := rfl

theorem rs_walk {σ : Val} (h : ∃ j < 8, σ (.n (val% «rs_eq_run» "r_g@3")) = ofK (addressOfIndex j)) :
    walk σ (Fn.body fn% «rs_eq_run») = .ret (rsPre.flatMap (flEvs σ)) [.n (val% «rs_eq_run» "s12#0")] := by
  rw [rs_eq_run_body, rsBody_split]
  exact walk_flat σ _ _ rs_flat (rs_dispOk h)

/-- `rs_eq_run`'s frames: `rs_eq_run_loop0`'s (entered unless `q = 0`), the remainder's. -/
noncomputable def rsCalls (σ : Val) : List Call :=
  [⟨name% «rs_eq_run_loop0», [.n (val% «rs_eq_run» "s8#2"), .n (val% «rs_eq_run» "q_g@3"), .n (val% «rs_eq_run» "chain"), .n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1")], [], decide (σ (.n (val% «rs_eq_run» "s8#1")) ≠ 0)⟩,
    ⟨["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD (logG (σ (.n (val% «rs_eq_run» "r_g@3")))) "",
      [.n (val% «rs_eq_run» "row"), .n (val% «rs_eq_run» "last~1"), .n (val% «rs_eq_run» "last~2")], [.n (val% «rs_eq_run» "last")], true⟩]

theorem rs_calls (σ : Val) : calls (rsPre.flatMap (flEvs σ)) = rsCalls σ := by
  rw [(flat_parts σ _ rs_flat).2.2.2.1, rs_callSF]
  rfl

theorem rsNames_getD (r : ℕ) (hr : r < 8) :
    ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD r "" = rsEqRowsNames.getD r "" := by
  interval_cases r <;> rfl

/-- A block of atoms each of which holds holds. -/
theorem rs_holdsList_of_atoms {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (l : List Stmt), l.all (fun s ↦ match s with | .atom _ => true | _ => false) = true →
      (∀ a, Stmt.atom a ∈ l → a.Holds rd σ) → Stmt.HoldsList C rd σ l True (fun _ ↦ True)
  | [], _, _ => trivial
  | s :: l, hl, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    match s, hl.1 with
    | .atom a, _ =>
      exact ⟨h a List.mem_cons_self,
        rs_holdsList_of_atoms l hl.2 fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

/-- **`q_g`, `r_g` and the count**: on a valuation satisfying `rsA`, `q_g = g^q`, `r_g = g^r`
and `count_g = g^(8q + r)`, `q, r < 8`. -/
theorem rsA_vals {rd : Reader} {σ : Val}
    (h : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ rsA True (fun _ ↦ True)) :
    ∃ q r : ℕ, q < 8 ∧ r < 8 ∧ σ (.n (val% «rs_eq_run» "q_g@3")) = gen ^ q ∧ σ (.n (val% «rs_eq_run» "r_g@3")) = gen ^ r ∧
      σ (.n (val% «rs_eq_run» "count_g")) = gen ^ (8 * q + r) := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  simp only [rsA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha⟩ := h
  have hbr : ∀ j < 3, σ (.n ((val% «rs_eq_run» "bits[0]") + j)) * σ (.n ((val% «rs_eq_run» "bits[0]") + j)) = σ (.n ((val% «rs_eq_run» "bits[0]") + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n ((val% «rs_eq_run» "bits[3]") + j)) * σ (.n ((val% «rs_eq_run» "bits[3]") + j)) = σ (.n ((val% «rs_eq_run» "bits[3]") + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n (val% «rs_eq_run» "r_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «rs_eq_run» "bits[0]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n (val% «rs_eq_run» "q_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «rs_eq_run» "bits[3]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  refine ⟨_, _, bitsVal_lt _ 3, bitsVal_lt _ 3, qg, rg, ?_⟩
  rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, ← pow_add, ← pow_add, ← pow_add,
    ← pow_add]
  congr 1; ring

/-- **The chain's size and the loop's guard**: on a valuation satisfying `rsAlloc` and `rsG`, with
`q_g = g^q`, the chain's size is `g^(64 (q + 2))`, and the guard is `1 + q_g`, its first argument
`1`. -/
theorem rsAllocG_vals {rd : Reader} {σ : Val} {q : ℕ} (hq : σ (.n (val% «rs_eq_run» "q_g@3")) = gen ^ q)
    (ha : ∀ a, Stmt.atom a ∈ rsAlloc ++ rsG → a.Holds rd σ) :
    σ (.n (val% «rs_eq_run» "chain~7")) = gen ^ (64 * (q + 2)) ∧
      σ (.n (val% «rs_eq_run» "s8#1")) = 1 + σ (.n (val% «rs_eq_run» "q_g@3")) ∧ σ (.n (val% «rs_eq_run» "s8#2")) = 1 := by
  have H : ∀ a, Stmt.atom a ∈ rsAlloc ++ rsG → a.Holds rd σ := ha
  have e0 := H (.const (.n (val% «rs_eq_run» "chain~0")) (word 4 0)) (by simp [rsAlloc])
  have e1 := H (.mul (.n (val% «rs_eq_run» "chain~1")) (.n (val% «rs_eq_run» "q_g@3")) (.n (val% «rs_eq_run» "chain~0"))) (by simp [rsAlloc])
  have e2 := H (.mul (.n (val% «rs_eq_run» "chain~2")) (.n (val% «rs_eq_run» "chain~1")) (.n (val% «rs_eq_run» "chain~1"))) (by simp [rsAlloc])
  have e3 := H (.mul (.n (val% «rs_eq_run» "chain~3")) (.n (val% «rs_eq_run» "chain~2")) (.n (val% «rs_eq_run» "chain~2"))) (by simp [rsAlloc])
  have e4 := H (.mul (.n (val% «rs_eq_run» "chain~4")) (.n (val% «rs_eq_run» "chain~3")) (.n (val% «rs_eq_run» "chain~3"))) (by simp [rsAlloc])
  have e5 := H (.mul (.n (val% «rs_eq_run» "chain~5")) (.n (val% «rs_eq_run» "chain~4")) (.n (val% «rs_eq_run» "chain~4"))) (by simp [rsAlloc])
  have e6 := H (.mul (.n (val% «rs_eq_run» "chain~6")) (.n (val% «rs_eq_run» "chain~5")) (.n (val% «rs_eq_run» "chain~5"))) (by simp [rsAlloc])
  have e7 := H (.mul (.n (val% «rs_eq_run» "chain~7")) (.n (val% «rs_eq_run» "chain~6")) (.n (val% «rs_eq_run» "chain~6"))) (by simp [rsAlloc])
  have g0 := H (.const (.n (val% «rs_eq_run» "s8#0")) (word 1 0)) (by simp [rsG])
  have g1 := H (.add (.n (val% «rs_eq_run» "s8#1")) (.n (val% «rs_eq_run» "s8#0")) (.n (val% «rs_eq_run» "q_g@3"))) (by simp [rsG])
  have g2 := H (.const (.n (val% «rs_eq_run» "s8#2")) (word 1 0)) (by simp [rsG])
  simp only [Atom.Holds] at e0 e1 e2 e3 e4 e5 e6 e7 g0 g1 g2
  refine ⟨?_, by rw [g1, g0, word_one], by rw [g2, word_one]⟩
  have w4 : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)
  rw [e7, e6, e5, e4, e3, e2, e1, e0, hq, w4, ← pow_add]
  simp only [← pow_add]
  congr 1; ring

variable {fs : String → ℕ}

/-- The atoms of `rs_eq_run`'s statements hold on its valid trees' valuations. -/
theorem rs_atoms_sub {l : List Stmt} (hl : ∀ s ∈ l, s ∈ rsPre) {rd : Reader} {σ : Val}
    (hes : ∀ e ∈ rsPre.flatMap (flEvs σ), e.Holds rd σ) : ∀ a, Stmt.atom a ∈ l → a.Holds rd σ :=
  fun a ha ↦ hes (.atom a) (List.mem_flatMap.mpr ⟨.atom a, hl _ ha,
    by rw [show flEvs σ (.atom a) = [.atom a] from rfl]; exact List.mem_singleton_self _⟩)

/-- **`rs_eq_run` is within its words**: on a count `g^c`, `c < 64`, its frame, `rs_eq_run_loop0`'s
run (`c / 8` iterations of at most `K6` words and its one phantom frame; its tail when skipped),
the remainder's `rs_eq_rows__L{c % 8}`, within `R`, and its chain of `64 (c / 8 + 2)` words. -/
theorem rs_totalLeOn {K6 R : ℕ} (htl : ∀ f, fs (Memory.tailKey f) ≤ fs f)
    (h6 : TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0»)
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) {c : ℕ}
    (hc : c < 64) :
    TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 2 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + (fs name% «rs_eq_run_loop0» + c / 8 * K6) + R + 64 * (c / 8 + 2)) := by
  intro rd t args rets hname h3 hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hname
  subst hname
  have hv' := hv
  obtain ⟨fn, hf, hpar, es, vs, hw, -, hes, -⟩ := hv'
  rw [find_rs_eq_run, Option.some.injEq] at hf
  subst hf
  have hd : ∃ j < 8, σ (.n (val% «rs_eq_run» "r_g@3")) = ofK (addressOfIndex j) := by
    by_contra hn
    rw [rs_walk_stuck σ hn] at hw
    cases hw
  rw [rs_walk hd, Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  obtain ⟨q, r, hq, hr, hg, rg, hcg⟩ :=
    rsA_vals (rs_holdsList_of_atoms (C := fun _ _ _ ↦ True) rsA rsA_atoms
      (rs_atoms_sub (fun s hs ↦ List.mem_append_left _ hs) hes))
  obtain ⟨hch, h43, h44⟩ := rsAllocG_vals hg (rs_atoms_sub (fun s hs ↦ by
    simp only [List.mem_append] at hs
    rw [rsPre_eq]
    simp only [rsPre0, List.mem_append]
    rcases hs with hs | hs
    · exact Or.inl (Or.inr (Or.inl hs))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hs))))) hes)
  have h3' : σ (.n (val% «rs_eq_run» "count_g")) = gen ^ c := by
    rw [← hpar] at h3
    exact h3
  have hqc : 8 * q + r = c := gen_pow_inj (by omega) (by omega) (hcg.symm.trans h3')
  have hc8 : c / 8 = q := by omega
  have hlog : logG (σ (.n (val% «rs_eq_run» "r_g@3"))) = r := by
    rw [rg, gen_pow_eq_ofK, logG_spec (by omega)]
  have hbufs : bufs = [64 * (q + 2)] := by
    have h := hb.1
    rw [Tree.events, Tree.name, find_rs_eq_run] at h
    simp only [Tree.val, rs_walk hd] at h
    rw [(flat_parts σ _ rs_flat).2.1, rs_allocSz] at h
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hch, gen_pow_eq_ofK] at h
    rw [h, logG_spec (by omega)]
  subst hbufs
  have htot := Budget.node_total_le fs
    (fun cl ↦ if cl.f = name% «rs_eq_run_loop0» then fs name% «rs_eq_run_loop0» + c / 8 * K6 else R)
    [fun _ ↦ True, fun _ ↦ True] (cs := rsCalls σ) hv hb
    (fun fn' es' vs' hf' hw' ↦ by
      rw [find_rs_eq_run, Option.some.injEq] at hf'
      subst hf'
      rw [rs_walk hd, Out.ret.injEq] at hw'
      rw [← hw'.1, rs_calls])
    (by simp [rsCalls]) (by rw [rsCalls]; rcases ks with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp [KidsT])
    (fun c' Q hc' ht t' rets' htn htv htb _ ↦ ?_)
  · refine htot.trans ?_
    simp only [rsCalls, Budget.callsT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ite_true, hlog, rsNames_getD r hr]
    have hne : rsEqRowsNames.getD r "" ≠ name% «rs_eq_run_loop0» := by interval_cases r <;> decide
    rw [ite_neg' hne, hc8]
    generalize q * K6 = X
    have htl0 := htl name% «rs_eq_run_loop0»
    have h1 : (if decide (σ (.n (val% «rs_eq_run» "s8#1")) ≠ 0) = true then fs name% «rs_eq_run_loop0» + X else fs
        (Memory.tailKey name% «rs_eq_run_loop0»)) ≤ fs name% «rs_eq_run_loop0» + X := by
      split <;> omega
    generalize (if decide (σ (.n (val% «rs_eq_run» "s8#1")) ≠ 0) = true then fs name% «rs_eq_run_loop0» + X else fs
        (Memory.tailKey name% «rs_eq_run_loop0»)) = Y at h1 ⊢
    generalize fs name% «rs_eq_run_loop0» + X = Z at h1 ⊢
    omega
  · simp only [rsCalls, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hc'
    rcases hc' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [decide_eq_true_eq] at ht
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · exfalso
          apply ht
          rw [h43, hg, h0, pow_zero]
          exact e_add_self 1
        · exact h0
      have := h6 rd t' _ rets' htn (by
        simp only [List.map_cons, List.map_nil, h44, hg]
        exact loopPre_gen hq0 (by omega) _) htv htb
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, hg,
        gen_pow_eq_ofK, logG_spec (show q < 2 ^ 64 - 1 by omega)] at this
      rw [ite_pos' rfl, hc8]
      generalize q * K6 = X at this ⊢
      omega
    · rw [hlog, rsNames_getD r hr] at htn ⊢
      have hne : rsEqRowsNames.getD r "" ≠ name% «rs_eq_run_loop0» := by interval_cases r <;> decide
      rw [ite_neg' hne]
      exact hR r hr rd t' _ rets' htn htv htb

/-- **`rs_eq_run` on at most `34` coordinates is within `fs "rs_eq_run" + (fs "rs_eq_run_loop0" + 4
· K6) + R + 384` words** (`rs_totalLeOn`, `c / 8 ≤ 4`). -/
theorem rs_totalLeOn34 {K6 R : ℕ} (htl : ∀ f, fs (Memory.tailKey f) ≤ fs f)
    (h6 : TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0»)
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) :
    ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 2 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + (fs name% «rs_eq_run_loop0» + 4 * K6) + R + 384) := by
  intro c hc rd t args rets hn hp hv hb
  have h := rs_totalLeOn htl h6 hR (c := c) (by omega) rd t args rets hn hp hv hb
  have := Nat.mul_le_mul_right K6 (show c / 8 ≤ 4 by omega)
  dsimp only at h ⊢
  generalize c / 8 * K6 = X at h this
  omega

end
end LeanVM.Guest.B1
