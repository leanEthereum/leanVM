/-
  LeanVM.Guest.B1.Eq.RsWords

  `rs_eq_run`'s words, by hand (it has no words certificate: its dispatch): on `count < 64`
  coordinates, its frame, its chain, `rs_eq_run_loop0`'s `count / 8` iterations (or
  `rs_eq_run_loop0`'s frame when it is skipped) and the remainder's `rs_eq_rows__L{count % 8}`.
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Core.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `rs_eq_run` within its words

On a valid tree of `rs_eq_run` at arguments whose count is `g^c`, `c < 64` (`TotalLeOn`): its
body is flat (`rsBody = (rsA ++ rsT0) ++ rsD :: [copy, ret]`), so its walk's events are its
statements' (the dispatch `rsD` names a callee: else the walk is stuck, `rs_walk_stuck`) and its
frames are `rs_eq_run_loop0`'s and the remainder's `rs_eq_rows__L{r}` (`rs_calls`); it allocates
its chain. Its first atoms (`rsA`, events of the walk) hold, so `q_g = σ 36 = g^q`, `r_g = σ 22 =
g^r`, `g^(8q + r) = count_g = g^c` (as in `rs_eq_run_sound`): `q = c / 8`, `r = c % 8`, and the
chain is `64 (q + 2)` words (`rs_bufs`). With `rs_eq_run_loop0`'s run's words (`TotalLeOn …
LoopPre`: `K6` per iteration and its one phantom frame, as `Count.wSKt_totalLeOn` gives it) and each
`rs_eq_rows__L{r}`, `r < 8`, within `R`, `rs_totalLeOn` bounds the tree by `fs "rs_eq_run" + (fs
"rs_eq_run_loop0" + c / 8 · K6) + R + 64 (c / 8 + 2)`; `rs_totalLeOn34`, for `c ≤ 34`, by
`fs "rs_eq_run" + (fs "rs_eq_run_loop0" + 4 · K6) + R + 384`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.Memory LeanVM.Core.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_run`'s atoms up to its chain: the count's bits, `r_g`, `q_g`, the check, the chain's
size and allocation. -/
def rsA : List Stmt := rsHead

/-- Row `0`'s stores, `rs_eq_run_loop0`'s call and the remainder's pointers. -/
def rsT0 : List Stmt := rsOnes ++
  [.atom (.const (.n 114) (word 1 0)), .atom (.add (.n 115) (.n 114) (.n 36)),
    .atom (.const (.n 116) (word 1 0)),
    .callIf (.n 115) name% «rs_eq_run_loop0» [.n 116, .n 36, .n 49, .n 0, .n 1],
    .atom (.mul (.n 117) (.n 36) (.n 36)), .atom (.mul (.n 118) (.n 117) (.n 117)),
    .atom (.mul (.n 119) (.n 118) (.n 118)), .atom (.mul (.n 120) (.n 36) (.n 36)),
    .atom (.mul (.n 121) (.n 120) (.n 120)), .atom (.mul (.n 122) (.n 121) (.n 121)),
    .atom (.mul (.n 123) (.n 122) (.n 122)), .atom (.mul (.n 124) (.n 123) (.n 123)),
    .atom (.mul (.n 125) (.n 124) (.n 124)), .atom (.mul (.n 126) (.n 49) (.n 125)),
    .atom (.mul (.n 127) (.n 0) (.n 119)), .atom (.mul (.n 128) (.n 1) (.n 119))]

/-- The remainder's dispatch. -/
def rsD : Stmt :=
  .dispatch (.n 22) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
    "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n 126, .n 127, .n 128]
    [.n 129]

/-- `rs_eq_run`'s statements after `rsA`, before its `ret`. -/
def rsT : List Stmt := rsT0 ++ [rsD, .atom (.copy (.n 130) (.n 129))]

theorem rsBody_split : rsBody = (rsA ++ rsT) ++ [.ret [.n 130]] := by
  simp only [rsBody, rsA, rsT, rsT0, List.append_assoc]; rfl

theorem rsBody_split' : rsBody = (rsA ++ rsT0) ++ (rsD :: [.atom (.copy (.n 130) (.n 129)),
    .ret [.n 130]]) := by
  simp only [rsBody, rsA, rsT0, List.append_assoc]; rfl

theorem rs_flat : (rsA ++ rsT).all Stmt.flat = true := by decide +kernel

theorem rsA_atoms : rsA.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem rs_noDispB : (rsA ++ rsT0).all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem rs_dispOk0 (σ : Val) : ∀ s ∈ rsA ++ rsT0, DispOk σ s := fun s hs ↦ by
  have := List.all_eq_true.mp rs_noDispB s hs
  cases s <;> simp_all [DispOk]

theorem rs_dispOk {σ : Val} (h : ∃ j < 8, σ (.n 22) = ofK (addressOfIndex j)) :
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
theorem rs_walk_stuck (σ : Val) (h : ¬ ∃ j < 8, σ (.n 22) = ofK (addressOfIndex j)) :
    walk σ (Fn.body fn% «rs_eq_run») = .stuck := by
  rw [rs_eq_run_body, rsBody_split']
  refine walk_flat_stuck σ _ _ (by decide +kernel) (rs_dispOk0 σ) ?_
  rw [walk, rsD, walk1, pick_stuck σ _ _ _ _ 0 fun i hi hx ↦ h ⟨i, by simpa using hi, by
    rwa [Nat.zero_add] at hx⟩]
  rfl

theorem rs_callSF (σ : Val) : (rsA ++ rsT).filterMap (Stmt.callSF σ) =
    [(some (.n 115), name% «rs_eq_run_loop0», [.n 116, .n 36, .n 49, .n 0, .n 1], []),
      (none, ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
        "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD
          (logG (σ (.n 22))) "", [.n 126, .n 127, .n 128], [.n 129])] := rfl

theorem rs_allocSz : (rsA ++ rsT).filterMap Main.Stmt.allocSz = [(.n 49, .inr (.n 48))] := rfl

theorem rs_walk {σ : Val} (h : ∃ j < 8, σ (.n 22) = ofK (addressOfIndex j)) :
    walk σ (Fn.body fn% «rs_eq_run») = .ret ((rsA ++ rsT).flatMap (flEvs σ)) [.n 130] := by
  rw [rs_eq_run_body, rsBody_split]
  exact walk_flat σ _ _ rs_flat (rs_dispOk h)

/-- `rs_eq_run`'s frames: `rs_eq_run_loop0`'s (entered unless `q = 0`), the remainder's. -/
noncomputable def rsCalls (σ : Val) : List Call :=
  [⟨name% «rs_eq_run_loop0», [.n 116, .n 36, .n 49, .n 0, .n 1], [], decide (σ (.n 115) ≠ 0)⟩,
    ⟨["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD (logG (σ (.n 22))) "",
      [.n 126, .n 127, .n 128], [.n 129], true⟩]

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

/-- **`q_g`, `r_g`, the count and the chain's size**: on a valuation satisfying `rsA`,
`σ 36 = g^q`, `σ 22 = g^r`, `σ 2 = g^(8q + r)`, `q, r < 8`, and `σ 48 = g^(64 (q + 2))`. -/
theorem rsA_vals {rd : Reader} {σ : Val}
    (h : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ rsA True (fun _ ↦ True)) :
    ∃ q r : ℕ, q < 8 ∧ r < 8 ∧ σ (.n 36) = gen ^ q ∧ σ (.n 22) = gen ^ r ∧
      σ (.n 2) = gen ^ (8 * q + r) ∧ σ (.n 48) = gen ^ (64 * (q + 2)) := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have w4 : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by norm_num)
  simp only [rsA, rsHead, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at h
  obtain ⟨b0, h9, h10, h11, h12, b1, h13, h14, h15, h16, h17, b2, h18, h19, h20, h21, h22,
    b3, h23, h24, h25, h26, b4, h27, h28, h29, h30, h31, b5, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, ha, h41, h42, h43, h44, h45, h46, h47, h48⟩ := h
  have hbr : ∀ j < 3, σ (.n (3 + j)) * σ (.n (3 + j)) = σ (.n (3 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n (6 + j)) * σ (.n (6 + j)) = σ (.n (6 + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n 22) = ∏ j ∈ Finset.range 3, (1 + σ (.n (3 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h22, h17, h12, h16, h21, h11, h15, h20, h9, h13, h18, h10, h14, h19, w3, w5, w17, word_one]
  have qg : σ (.n 36) = ∏ j ∈ Finset.range 3, (1 + σ (.n (6 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h36, h31, h26, h30, h35, h25, h29, h34, h23, h27, h32, h24, h28, h33, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  refine ⟨_, _, bitsVal_lt _ 3, bitsVal_lt _ 3, qg, rg, ?_, ?_⟩
  · rw [← e_add_eq_zero_iff.mp ha, h40, h39, h38, h37, qg, rg, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  · rw [h48, h47, h46, h45, h44, h43, h42, h41, w4, qg]
    ring

/-- The chain's words: `64 (q + 2)`. -/
theorem rs_bufs {σ : Val} {bufs : List ℕ} {ks : List Tree}
    (hd : ∃ j < 8, σ (.n 22) = ofK (addressOfIndex j))
    (hb : (Memory.Tree.node "rs_eq_run" σ bufs ks).BufsOk coreProgram) {q : ℕ} (hq : q < 8)
    (h48 : σ (.n 48) = gen ^ (64 * (q + 2))) : bufs = [64 * (q + 2)] := by
  have h := hb.1
  rw [Tree.events, Tree.name, find_rs_eq_run] at h
  simp only [Tree.val, rs_walk hd] at h
  rw [(flat_parts σ _ rs_flat).2.1, rs_allocSz] at h
  rw [h]
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, h48, gen_pow_eq_ofK]
  rw [logG_spec (by omega)]

variable {fs : String → ℕ}

/-- **`rs_eq_run` is within its words**: on a count `g^c`, `c < 64`, its frame, its chain
(`64 (c / 8 + 2)` words), `rs_eq_run_loop0`'s run (`c / 8` iterations of at most `K6` words and its
one phantom frame; its frame when skipped) and the remainder's `rs_eq_rows__L{c % 8}`, within `R`. -/
theorem rs_totalLeOn {K6 R : ℕ}
    (h6 : TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0»)
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) {c : ℕ}
    (hc : c < 64) :
    TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 2 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + (fs name% «rs_eq_run_loop0» + c / 8 * K6) + R +
        64 * (c / 8 + 2)) := by
  intro rd t args rets hname h2 hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hname
  subst hname
  have hv' := hv
  obtain ⟨fn, hf, hpar, es, vs, hw, -, hes, -⟩ := hv'
  rw [find_rs_eq_run, Option.some.injEq] at hf
  subst hf
  have hd : ∃ j < 8, σ (.n 22) = ofK (addressOfIndex j) := by
    by_contra hn
    rw [rs_walk_stuck σ hn] at hw
    cases hw
  rw [rs_walk hd, Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  have hev : ∀ a, Stmt.atom a ∈ rsA ++ rsT → a.Holds rd σ := fun a ha ↦
    hes (.atom a) (List.mem_flatMap.mpr ⟨.atom a, ha,
      by rw [show flEvs σ (.atom a) = [.atom a] from rfl]; exact List.mem_singleton_self _⟩)
  have hA : ∀ a, Stmt.atom a ∈ rsA → a.Holds rd σ := fun a ha ↦ hev a (List.mem_append_left _ ha)
  have hT : ∀ a, Stmt.atom a ∈ rsT0 → a.Holds rd σ := fun a ha ↦
    hev a (List.mem_append_right _ (List.mem_append_left _ ha))
  have h114 : σ (.n 114) = 1 := by
    have := hT (.const (.n 114) (word 1 0)) (by simp [rsT0])
    simpa [Atom.Holds, word_one] using this
  have h115 : σ (.n 115) = σ (.n 114) + σ (.n 36) := hT (.add (.n 115) (.n 114) (.n 36))
    (by simp [rsT0])
  have h116 : σ (.n 116) = 1 := by
    have := hT (.const (.n 116) (word 1 0)) (by simp [rsT0])
    simpa [Atom.Holds, word_one] using this
  obtain ⟨q, r, hq, hr, hg, rg, hcg, h48⟩ :=
    rsA_vals (rs_holdsList_of_atoms (C := fun _ _ _ ↦ True) rsA rsA_atoms hA)
  have h2' : σ (.n 2) = gen ^ c := by
    rw [← hpar] at h2
    exact h2
  have hqc : 8 * q + r = c := gen_pow_inj (by omega) (by omega) (hcg.symm.trans h2')
  have hc8 : c / 8 = q := by omega
  have hlog : logG (σ (.n 22)) = r := by
    rw [rg, gen_pow_eq_ofK, logG_spec (by omega)]
  have hbufs := rs_bufs hd hb hq h48
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
    have h1 : (if decide (σ (.n 115) ≠ 0) = true then fs name% «rs_eq_run_loop0» + X else fs
        name% «rs_eq_run_loop0») ≤
        fs name% «rs_eq_run_loop0» + X := by
      split <;> simp
    generalize (if decide (σ (.n 115) ≠ 0) = true then fs name% «rs_eq_run_loop0» + X else fs
        name% «rs_eq_run_loop0») = Y at h1 ⊢
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
          rw [h115, h114, hg, h0, pow_zero]
          exact e_add_self 1
        · exact h0
      have := h6 rd t' _ rets' htn (by
        simp only [List.map_cons, List.map_nil, h116, hg]
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

/-- **`rs_eq_run` on at most `34` coordinates is within `fs "rs_eq_run" + (fs "rs_eq_run_loop0" +
4 · K6) + R + 384` words** (`rs_totalLeOn`, `c / 8 ≤ 4`). -/
theorem rs_totalLeOn34 {K6 R : ℕ}
    (h6 : TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0»)
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) :
    ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 2 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + (fs name% «rs_eq_run_loop0» + 4 * K6) + R + 384) := by
  intro c hc rd t args rets hn hp hv hb
  have h := rs_totalLeOn h6 hR (c := c) (by omega) rd t args rets hn hp hv hb
  have := Nat.mul_le_mul_right K6 (show c / 8 ≤ 4 by omega)
  have h4 : c / 8 ≤ 4 := by omega
  dsimp only at h ⊢
  generalize c / 8 * K6 = X at h this
  omega

end
end LeanVM.Guest.B1
