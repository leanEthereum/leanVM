/-
  LeanVM.Guest.B1.Eq.RsWords

  `rs_eq_run`'s words, by hand (it has no words certificate: its dispatch): on `count < 64`
  coordinates, its frame, `__loop5`'s `count / 8` iterations (or `__loop5`'s frame when it is
  skipped) and the remainder's `rs_eq_rows__L{count % 8}`.
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.Memory.LoopPre

/-!
# `rs_eq_run` within its words

On a valid tree of `rs_eq_run` at arguments whose count is `g^c`, `c < 64` (`TotalLeOn`): its
body is flat (`rsBody = (rsA ++ rsT0) ++ rsD :: [copy, ret]`), so its walk's events are its
statements' (the dispatch `rsD` names a callee: else the walk is stuck, `rs_walk_stuck`) and its
frames are `__loop5`'s and the remainder's `rs_eq_rows__L{r}` (`rs_calls`); it allocates nothing.
Its first `43` atoms (`rsA`, events of the walk) hold, so `q_g = σ 37 = g^q`, `r_g = σ 23 = g^r`
and `g^(8q + r) = count_g = g^c` (as in `rs_eq_run_sound`): `q = c / 8`, `r = c % 8`. With
`__loop5`'s run's words (`TotalLeOn … LoopPre`: `K6` per iteration and its one phantom frame, as
`Count.wSKt_totalLeOn` gives it) and each `rs_eq_rows__L{r}`, `r < 8`, within `R`, `rs_totalLeOn`
bounds the tree by `fs "rs_eq_run" + (fs "__loop5" + c / 8 · K6) + R`; `rs_totalLeOn34`, for
`c ≤ 34`, by `fs "rs_eq_run" + (fs "__loop5" + 4 · K6) + R`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_run`'s atoms before `__loop5`: the count's bits, `r_g`, `q_g`, the check. -/
def rsA : List Stmt :=
  [.atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.const (.n 10) (word 1 0)),
    .atom (.const (.n 11) (word 3 0)), .atom (.mul (.n 12) (.n 4) (.n 11)),
    .atom (.add (.n 13) (.n 10) (.n 12)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.const (.n 14) (word 1 0)), .atom (.const (.n 15) (word 5 0)),
    .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.add (.n 17) (.n 14) (.n 16)),
    .atom (.mul (.n 18) (.n 13) (.n 17)), .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.const (.n 19) (word 1 0)), .atom (.const (.n 20) (word 17 0)),
    .atom (.mul (.n 21) (.n 6) (.n 20)), .atom (.add (.n 22) (.n 19) (.n 21)),
    .atom (.mul (.n 23) (.n 18) (.n 22)), .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.const (.n 24) (word 1 0)), .atom (.const (.n 25) (word 3 0)),
    .atom (.mul (.n 26) (.n 7) (.n 25)), .atom (.add (.n 27) (.n 24) (.n 26)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 28) (word 1 0)),
    .atom (.const (.n 29) (word 5 0)), .atom (.mul (.n 30) (.n 8) (.n 29)),
    .atom (.add (.n 31) (.n 28) (.n 30)), .atom (.mul (.n 32) (.n 27) (.n 31)),
    .atom (.mul (.n 9) (.n 9) (.n 9)), .atom (.const (.n 33) (word 1 0)),
    .atom (.const (.n 34) (word 17 0)), .atom (.mul (.n 35) (.n 9) (.n 34)),
    .atom (.add (.n 36) (.n 33) (.n 35)), .atom (.mul (.n 37) (.n 32) (.n 36)),
    .atom (.mul (.n 38) (.n 37) (.n 37)), .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)), .atom (.mul (.n 41) (.n 40) (.n 23)),
    .atom (.assertEq (.n 41) (.n 3)), .atom (.const (.n 42) (word 1 0)),
    .atom (.add (.n 43) (.n 42) (.n 37)), .atom (.const (.n 44) (word 1 0))]

/-- `__loop5`'s call and the remainder's pointers. -/
def rsT0 : List Stmt :=
  [.callIf (.n 43) "__loop5" [.n 44, .n 37, .n 0, .n 1, .n 2],
    .atom (.mul (.n 45) (.n 37) (.n 37)), .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)), .atom (.mul (.n 48) (.n 37) (.n 37)),
    .atom (.mul (.n 49) (.n 48) (.n 48)), .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)), .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 52) (.n 52)), .atom (.mul (.n 54) (.n 0) (.n 53)),
    .atom (.mul (.n 55) (.n 1) (.n 47)), .atom (.mul (.n 56) (.n 2) (.n 47))]

/-- The remainder's dispatch. -/
def rsD : Stmt :=
  .dispatch (.n 23) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n 54, .n 55, .n 56] [.n 57]

/-- `rs_eq_run`'s statements after `rsA`, before its `ret`. -/
def rsT : List Stmt := rsT0 ++ [rsD, .atom (.copy (.n 58) (.n 57))]

theorem rsBody_split : rsBody = (rsA ++ rsT) ++ [.ret [.n 58]] := rfl

theorem rsBody_split' : rsBody = (rsA ++ rsT0) ++ (rsD :: [.atom (.copy (.n 58) (.n 57)), .ret [.n 58]]) := rfl

theorem rs_flat : (rsA ++ rsT).all Stmt.flat = true := by decide +kernel

theorem rsA_atoms : rsA.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem rs_noDispB : (rsA ++ rsT0).all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem rs_dispOk0 (σ : Val) : ∀ s ∈ rsA ++ rsT0, DispOk σ s := fun s hs ↦ by
  have := List.all_eq_true.mp rs_noDispB s hs
  cases s <;> simp_all [DispOk]

theorem rs_dispOk {σ : Val} (h : ∃ j < 8, σ (.n 23) = ofK (addressOfIndex j)) :
    ∀ s ∈ rsA ++ rsT, DispOk σ s := by
  intro s hs
  simp only [rsT, ← List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with (hs | hs) | rfl | rfl
  · exact rs_dispOk0 σ s (List.mem_append_left _ hs)
  · exact rs_dispOk0 σ s (List.mem_append_right _ hs)
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
theorem rs_walk_stuck (σ : Val) (h : ¬ ∃ j < 8, σ (.n 23) = ofK (addressOfIndex j)) :
    walk σ (Fn.body Data.core5) = .stuck := by
  rw [core5_body, rsBody_split']
  refine walk_flat_stuck σ _ _ (by decide +kernel) (rs_dispOk0 σ) ?_
  rw [walk, rsD, walk1, pick_stuck σ _ _ _ _ 0 fun i hi hx ↦ h ⟨i, by simpa using hi, by
    rwa [Nat.zero_add] at hx⟩]
  rfl

theorem rs_callSF (σ : Val) : (rsA ++ rsT).filterMap (Stmt.callSF σ) =
    [(some (.n 43), "__loop5", [.n 44, .n 37, .n 0, .n 1, .n 2], []),
      (none, ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
        "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD
          (logG (σ (.n 23))) "", [.n 54, .n 55, .n 56], [.n 57])] := rfl

theorem rs_allocSz : (rsA ++ rsT).filterMap Main.Stmt.allocSz = [] := rfl

theorem rs_walk {σ : Val} (h : ∃ j < 8, σ (.n 23) = ofK (addressOfIndex j)) :
    walk σ (Fn.body Data.core5) = .ret ((rsA ++ rsT).flatMap (flEvs σ)) [.n 58] := by
  rw [core5_body, rsBody_split]
  exact walk_flat σ _ _ rs_flat (rs_dispOk h)

/-- `rs_eq_run`'s frames: `__loop5`'s (entered unless `q = 0`), the remainder's. -/
noncomputable def rsCalls (σ : Val) : List Call :=
  [⟨"__loop5", [.n 44, .n 37, .n 0, .n 1, .n 2], [], decide (σ (.n 43) ≠ 0)⟩,
    ⟨["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD (logG (σ (.n 23))) "",
      [.n 54, .n 55, .n 56], [.n 57], true⟩]

theorem rs_calls (σ : Val) : calls ((rsA ++ rsT).flatMap (flEvs σ)) = rsCalls σ := by
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

/-- **`q_g`, `r_g` and the count**: on a valuation satisfying `rsA`, `σ 37 = g^q`, `σ 23 = g^r`
and `σ 3 = g^(8q + r)`, `q, r < 8`. -/
theorem rsA_vals {rd : Reader} {σ : Val}
    (h : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ rsA True (fun _ ↦ True)) :
    ∃ q r : ℕ, q < 8 ∧ r < 8 ∧ σ (.n 37) = gen ^ q ∧ σ (.n 23) = gen ^ r ∧
      σ (.n 3) = gen ^ (8 * q + r) ∧ σ (.n 43) = 1 + σ (.n 37) ∧ σ (.n 44) = 1 := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  simp only [rsA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, h42, h43, h44⟩ := h
  have hbr : ∀ j < 3, σ (.n (4 + j)) * σ (.n (4 + j)) = σ (.n (4 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n (7 + j)) * σ (.n (7 + j)) = σ (.n (7 + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n 23) = ∏ j ∈ Finset.range 3, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n 37) = ∏ j ∈ Finset.range 3, (1 + σ (.n (7 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  refine ⟨_, _, bitsVal_lt _ 3, bitsVal_lt _ 3, qg, rg, ?_, by rw [h43, h42, word_one],
    by rw [h44, word_one]⟩
  rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, ← pow_add, ← pow_add, ← pow_add,
    ← pow_add]
  congr 1; ring

variable {fs : String → ℕ}

/-- **`rs_eq_run` is within its words**: on a count `g^c`, `c < 64`, its frame, `__loop5`'s run
(`c / 8` iterations of at most `K6` words and its one phantom frame; its frame when skipped) and the
remainder's `rs_eq_rows__L{c % 8}`, within `R`. -/
theorem rs_totalLeOn {K6 R : ℕ}
    (h6 : TotalLeOn coreProgram fs "__loop5" LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs "__loop5")
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) {c : ℕ}
    (hc : c < 64) :
    TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + (fs "__loop5" + c / 8 * K6) + R) := by
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
  have hd : ∃ j < 8, σ (.n 23) = ofK (addressOfIndex j) := by
    by_contra hn
    rw [rs_walk_stuck σ hn] at hw
    cases hw
  rw [rs_walk hd, Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  have hA : ∀ a, Stmt.atom a ∈ rsA → a.Holds rd σ := fun a ha ↦
    hes (.atom a) (List.mem_flatMap.mpr ⟨.atom a, List.mem_append_left _ ha,
      by rw [show flEvs σ (.atom a) = [.atom a] from rfl]; exact List.mem_singleton_self _⟩)
  obtain ⟨q, r, hq, hr, hg, rg, hcg, h43, h44⟩ :=
    rsA_vals (rs_holdsList_of_atoms (C := fun _ _ _ ↦ True) rsA rsA_atoms hA)
  have h3' : σ (.n 3) = gen ^ c := by
    rw [← hpar] at h3
    exact h3
  have hqc : 8 * q + r = c := gen_pow_inj (by omega) (by omega) (hcg.symm.trans h3')
  have hc8 : c / 8 = q := by omega
  have hlog : logG (σ (.n 23)) = r := by
    rw [rg, gen_pow_eq_ofK, logG_spec (by omega)]
  have hbufs : bufs = [] := by
    have h := hb.1
    rw [Tree.events, Tree.name, find_rs_eq_run] at h
    simp only [Tree.val, rs_walk hd] at h
    rw [(flat_parts σ _ rs_flat).2.1, rs_allocSz] at h
    simpa using h
  subst hbufs
  have htot := Budget.node_total_le fs
    (fun cl ↦ if cl.f = "__loop5" then fs "__loop5" + c / 8 * K6 else R)
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
    have hne : rsEqRowsNames.getD r "" ≠ "__loop5" := by interval_cases r <;> decide
    rw [ite_neg' hne]
    generalize c / 8 * K6 = X
    have h1 : (if decide (σ (.n 43) ≠ 0) = true then fs "__loop5" + X else fs "__loop5") ≤
        fs "__loop5" + X := by
      split <;> simp
    generalize (if decide (σ (.n 43) ≠ 0) = true then fs "__loop5" + X else fs "__loop5") = Y at h1 ⊢
    generalize fs "__loop5" + X = Z at h1 ⊢
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
      have hne : rsEqRowsNames.getD r "" ≠ "__loop5" := by interval_cases r <;> decide
      rw [ite_neg' hne]
      exact hR r hr rd t' _ rets' htn htv htb

/-- **`rs_eq_run` on at most `34` coordinates is within `fs "rs_eq_run" + (fs "__loop5" + 4 · K6) +
R` words** (`rs_totalLeOn`, `c / 8 ≤ 4`). -/
theorem rs_totalLeOn34 {K6 R : ℕ}
    (h6 : TotalLeOn coreProgram fs "__loop5" LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs "__loop5")
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) :
    ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + (fs "__loop5" + 4 * K6) + R) := by
  intro c hc rd t args rets hn hp hv hb
  have h := rs_totalLeOn h6 hR (c := c) (by omega) rd t args rets hn hp hv hb
  have := Nat.mul_le_mul_right K6 (show c / 8 ≤ 4 by omega)
  dsimp only at h ⊢
  generalize c / 8 * K6 = X at h this
  omega

end
end LeanVM.Guest.B1
