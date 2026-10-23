/-
  LeanVM.Guest.B1.Whir.ResIter

  `open_stacked`'s residual loop at its honest valuation, and its relation from its queries'
  memory.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLoops
public import LeanVM.Guest.B1.Whir.QueriesComplete

/-!
# The residual loop, honestly (TRIAGE #36)

`resIterVal`: the valuation of the residual loop's body at `x`, from the query's position `ch0`,
the basis rows `A`, `B`, the chain's entry `r0` and the query's weight `wq`. `resIter_holds`: the
body holds on a memory holding them and the chain's next entry. `resLoop_rel`: the loop from
iteration `j` holds when every query from `j` on finds its memory.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The running product of a query's factors over the coordinates below `t + 1`. -/
def resPre (A B : ℕ → E) (vals : List ℕ) (ch0 : E) (t : ℕ) : E :=
  ∏ s ∈ Finset.range (t + 1), (A s + B s * resChain vals ch0 s)

/-- The values of coordinate `t + 1`'s step (`resStep`). -/
def resStepVals (A B : ℕ → E) (vals : List ℕ) (ch0 : E) (t : ℕ) : List E :=
  [eOfNat (vals.getD t 0), resChain vals ch0 t + eOfNat (vals.getD t 0), resChain vals ch0 (t + 1), A (t + 1),
    B (t + 1), B (t + 1) * resChain vals ch0 (t + 1), A (t + 1) + B (t + 1) * resChain vals ch0 (t + 1),
    resPre A B vals ch0 (t + 1)]

/-- **The residual loop's body's valuation at `x`**. -/
def resIterVal (cols : ℕ) (vals : List ℕ) (x N qpos ba bb rc qw : E) (ch0 : E) (A B : ℕ → E) (r0 wq : E) : Val :=
  setl (Val.ofArgs [x, N, qpos, ba, bb, rc, qw]) 7
    ([qpos * x, ch0, A 0, B 0, B 0 * ch0, A 0 + B 0 * ch0] ++
      ((List.range (cols - 1)).map (resStepVals A B vals ch0)).flatten ++
      [rc * x, r0, qw * x, wq, wq * resPre A B vals ch0 (cols - 1), r0 + wq * resPre A B vals ch0 (cols - 1),
        rc * x, gen, x * gen, x * gen + N, gen, x * gen])

theorem resPre_zero (A B : ℕ → E) (vals : List ℕ) (ch0 : E) :
    resPre A B vals ch0 0 = A 0 + B 0 * ch0 := by simp [resPre, resChain]

theorem resPre_succ (A B : ℕ → E) (vals : List ℕ) (ch0 : E) (t : ℕ) :
    resPre A B vals ch0 (t + 1) = resPre A B vals ch0 t * (A (t + 1) + B (t + 1) * resChain vals ch0 (t + 1)) := by
  rw [resPre, Finset.prod_range_succ]; rfl

theorem resPre_eq (A B : ℕ → E) (vals : List ℕ) (ch0 : E) {cols : ℕ} (hc : 1 ≤ cols) :
    resPre A B vals ch0 (cols - 1) = resProd A B vals ch0 cols := by
  rw [resPre, resProd, show cols - 1 + 1 = cols by omega]

/-- **One query's body holds** at `resIterVal`, on a memory holding its position, its basis rows,
the chain's entry, its weight and the chain's next entry. -/
theorem resIter_holds {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} (hc : 1 ≤ cols)
    {x N qpos ba bb rc qw ch0 r0 wq : E} {A B : ℕ → E}
    (lp : LoadHolds rd (qpos * x) posOff ch0) (la : ∀ t < cols, LoadHolds rd ba (row + t) (A t))
    (lb : ∀ t < cols, LoadHolds rd bb (row + t) (B t)) (lr : LoadHolds rd (rc * x) 0 r0)
    (lw : LoadHolds rd (qw * x) qo wq)
    (lr1 : LoadHolds rd (rc * x) 1 (r0 + wq * resProd A B vals ch0 cols)) (hK : IsInK (x * gen + N))
    (hcall : x * gen + N ≠ 0 → C loop [x * gen, N, qpos, ba, bb, rc, qw] []) :
    Stmt.HoldsList C rd (resIterVal cols vals x N qpos ba bb rc qw ch0 A B r0 wq)
      (resLoopBody posOff row cols qo vals loop) False (fun rs => rs = []) := by
  set H : List E := [qpos * x, ch0, A 0, B 0, B 0 * ch0, A 0 + B 0 * ch0] with hH
  set M : List E := ((List.range (cols - 1)).map (resStepVals A B vals ch0)).flatten with hM
  set pe := resPre A B vals ch0 (cols - 1)
  set T : List E := [rc * x, r0, qw * x, wq, wq * pe, r0 + wq * pe, rc * x, gen, x * gen, x * gen + N, gen,
    x * gen] with hT
  set σ := resIterVal cols vals x N qpos ba bb rc qw ch0 A B r0 wq with hσ
  have hσ' : σ = setl (Val.ofArgs [x, N, qpos, ba, bb, rc, qw]) 7 (H ++ (M ++ T)) := by
    rw [hσ, resIterVal, List.append_assoc]
  have lM : M.length = 8 * (cols - 1) := oq_length_flatten_uniform _ 8 (fun _ => rfl) _
  have lH : H.length = 6 := rfl
  have lT : T.length = 12 := rfl
  have larg : ∀ i < 7, σ (.n i) = [x, N, qpos, ba, bb, rc, qw].getD i 0 := fun i hi => by
    rw [hσ']; simp only [setl]; rw [set_n_lt (by omega)]; rfl
  have lv : ∀ off < (H ++ (M ++ T)).length, σ (.n (7 + off)) = (H ++ (M ++ T)).getD off 0 := fun off ho => by
    rw [hσ']; simp only [setl]; rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hlen : (H ++ (M ++ T)).length = 18 + 8 * (cols - 1) := by simp only [List.length_append, lH, lM, lT]; omega
  have skip : ∀ (l l' : List E) (n : ℕ), (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := fun l l' n => by
    rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have gH : ∀ t < 6, σ (.n (7 + t)) = H.getD t 0 := fun t ht => by
    rw [lv t (by omega), oq_getD_app_lt (by omega)]
  have gM : ∀ t < cols - 1, ∀ c < 8, σ (.n (13 + 8 * t + c)) = (resStepVals A B vals ch0 t).getD c 0 :=
    fun t ht c hc => by
    rw [show 13 + 8 * t + c = 7 + (H.length + (8 * t + c)) by rw [lH]; ring, lv _ (by omega), skip,
      oq_getD_app_lt (by omega), hM, oq_getD_flatten_uniform _ 8 (fun _ => rfl) _ _ _ ht hc]
  have gT : ∀ c < 12, σ (.n (13 + 8 * (cols - 1) + c)) = T.getD c 0 := fun c hc => by
    rw [show 13 + 8 * (cols - 1) + c = 7 + (H.length + (M.length + c)) by rw [lH, lM]; ring, lv _ (by omega),
      skip, skip]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = qpos := larg 2 (by omega)
  have a3 : σ (.n 3) = ba := larg 3 (by omega)
  have a4 : σ (.n 4) = bb := larg 4 (by omega)
  have a5 : σ (.n 5) = rc := larg 5 (by omega)
  have a6 : σ (.n 6) = qw := larg 6 (by omega)
  have h0 := gH 0 (by omega); have h1 := gH 1 (by omega); have h2 := gH 2 (by omega)
  have h3 := gH 3 (by omega); have h4 := gH 4 (by omega); have h5 := gH 5 (by omega)
  simp only [hH, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5
  -- the chain and the product after each coordinate
  have hch : ∀ t, t < cols → σ (.n (resChIdx t)) = resChain vals ch0 t ∧
      σ (.n (8 * t + 12)) = resPre A B vals ch0 t := by
    intro t ht
    rcases t with _ | t
    · exact ⟨h1, by rw [Nat.mul_zero, Nat.zero_add, h5, resPre_zero]⟩
    · have e2 := gM t (by omega) 2 (by omega)
      have e7 := gM t (by omega) 7 (by omega)
      simp only [resStepVals, List.getD_cons_zero, List.getD_cons_succ] at e2 e7
      refine ⟨by rw [show resChIdx (t + 1) = 13 + 8 * t + 2 by unfold resChIdx; split <;> omega, e2], ?_⟩
      rw [show 8 * (t + 1) + 12 = 13 + 8 * t + 7 by ring, e7]
  have hpe : σ (.n (if cols = 1 then 12 else 13 + 8 * (cols - 1) - 1)) = pe := by
    rw [show (if cols = 1 then 12 else 13 + 8 * (cols - 1) - 1) = 8 * (cols - 1) + 12 by split <;> omega]
    exact (hch (cols - 1) (by omega)).2
  rw [resLoopBody]
  simp only [holdsList_append]
  refine (holdsList_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨by rw [h0, a2, a0], by rw [h0, h1]; exact lp, by rw [a3, h2]; simpa using la 0 hc,
      by rw [a4, h3]; simpa using lb 0 hc, by rw [h4, h3, h1], by rw [h5, h2, h4]⟩
  rw [holdsList_range_flatten _ _ (fun t => resStep_noRet _ _ _)]
  refine ⟨fun t ht => ?_, ?_⟩
  · have e := fun c (hc : c < 8) => gM t ht c hc
    have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
    have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
    have e6 := e 6 (by omega); have e7 := e 7 (by omega)
    simp only [resStepVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7
    have hchp := hch t (by omega)
    have hk : 13 + 8 * (t + 1 - 1) = 13 + 8 * t := by omega
    have hcv : (if t + 1 = 1 then 8 else 13 + 8 * t - 6) = resChIdx t := by
      unfold resChIdx; split <;> split <;> omega
    have hpv : (if t + 1 = 1 then 12 else 13 + 8 * t - 1) = 8 * t + 12 := by split <;> omega
    simp only [resStep, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, hk, hcv, hpv]
    refine ⟨by rw [e0, word_eOfNat], by rw [e1, hchp.1, e0], by rw [e2, hchp.1, e1, resChain], ?_, ?_,
      by rw [e5, e4, e2], by rw [e6, e3, e5], by rw [e7, hchp.2, e6, resPre_succ]⟩
    · rw [a3, e3]; exact la (t + 1) (by omega)
    · rw [a4, e4]; exact lb (t + 1) (by omega)
  · have t0 := gT 0 (by omega); have t1 := gT 1 (by omega); have t2 := gT 2 (by omega)
    have t3 := gT 3 (by omega); have t4 := gT 4 (by omega); have t5 := gT 5 (by omega)
    have t6 := gT 6 (by omega); have t7 := gT 7 (by omega); have t8 := gT 8 (by omega)
    have t9 := gT 9 (by omega); have t10 := gT 10 (by omega); have t11 := gT 11 (by omega)
    simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
    refine ⟨by rw [t0, a5, a0], by rw [t0, t1]; exact lr, by rw [t2, a6, a0], by rw [t2, t3]; exact lw,
      by rw [t4, t3, hpe], by rw [t5, t1, t4], by rw [t6, a5, a0], ?_, t7, by rw [t8, a0, t7],
      by rw [t9, t8, a1], t10, by rw [t11, a0, t10], by rw [t9]; exact hK, fun h => ?_, trivial⟩
    · rw [t6, t5, ← resPre_eq A B vals ch0 hc] at *
      exact lr1
    · rw [t11, a1, a2, a3, a4, a5, a6]
      exact hcall (by rwa [t9] at h)

/-- **The residual loop from iteration `j`**: when every query `i` from `j` below `n` finds its
position, basis rows, chain entries and weight, the loop holds. -/
theorem resLoop_rel {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} {fn : Fn}
    (hfind : coreProgram.find? loop = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hb : fn.body = resLoopBody posOff row cols qo vals loop) (hc : 1 ≤ cols) {n : ℕ} (hn : n < ordG)
    {qpos ba bb rc qw : E} {ch0 r wq : ℕ → E} {A B : ℕ → E}
    (lp : ∀ i < n, LoadHolds rd (qpos * gen ^ i) posOff (ch0 i))
    (la : ∀ t < cols, LoadHolds rd ba (row + t) (A t)) (lb : ∀ t < cols, LoadHolds rd bb (row + t) (B t))
    (lr : ∀ i < n, LoadHolds rd (rc * gen ^ i) 0 (r i)) (lw : ∀ i < n, LoadHolds rd (qw * gen ^ i) qo (wq i))
    (lr1 : ∀ i < n, LoadHolds rd (rc * gen ^ i) 1 (r i + wq i * resProd A B vals (ch0 i) cols)) :
    ∀ j < n, coreProgram.Rel rd loop [gen ^ j, gen ^ n, qpos, ba, bb, rc, qw] [] := by
  have hn' : n < 2 ^ 64 - 1 := hn
  suffices H : ∀ t j, j + t + 1 = n →
      coreProgram.relN rd (t + 1) loop [gen ^ j, gen ^ n, qpos, ba, bb, rc, qw] [] from
    fun j hj => ⟨_, H (n - j - 1) j (by omega)⟩
  intro t
  induction t with
  | zero =>
    intro j hj
    rw [relN_succ_iff hfind]
    refine ⟨resIterVal cols vals (gen ^ j) (gen ^ n) qpos ba bb rc qw (ch0 j) A B (r j) (wq j), ?_, ?_⟩
    · rw [hp]; rfl
    · rw [hb]
      have h0 : gen ^ j * gen + gen ^ n = 0 := by rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      exact resIter_holds hc (lp j (by omega)) la lb (lr j (by omega)) (lw j (by omega)) (lr1 j (by omega))
        (by rw [h0]; exact (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩) (fun h => absurd h0 h)
  | succ t ih =>
    intro j hj
    rw [relN_succ_iff hfind]
    refine ⟨resIterVal cols vals (gen ^ j) (gen ^ n) qpos ba bb rc qw (ch0 j) A B (r j) (wq j), ?_, ?_⟩
    · rw [hp]; rfl
    · rw [hb]
      refine resIter_holds hc (lp j (by omega)) la lb (lr j (by omega)) (lw j (by omega)) (lr1 j (by omega))
        (isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _)) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (j + 1) (by omega)

end
end LeanVM.Guest.B1
