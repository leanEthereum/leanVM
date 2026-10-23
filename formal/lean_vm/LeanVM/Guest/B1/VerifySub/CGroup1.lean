/-
  LeanVM.Guest.B1.VerifySub.CGroup1

  Group 1's allocating callees of `verify_sub`, placed: `g_power_of_word__L6` and
  `log2_ceil_in_the_exponent__*`, in the uniform form (`CompleteAt`).
-/

module

public import LeanVM.Guest.B1.VerifySub.CRel

/-!
# `g_power_of_word__L6`, placed

`gpw_holds_at`: the honest valuation of `g_power_of_word`'s body (`Exponent.lean`'s), with its
bit buffer at a given pointer `p`. `gpw6_completeAt`: at every frame pointer, the bit buffer is
the function's one `HeapBuf`, the table words it reads the caller's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`g_power_of_word`'s honest valuation at the bit buffer `p`.** -/
theorem gpw_holds_at {C : CallRel} (n : ℕ) (hn : n < 34) (rd : Reader) (value sq p : E)
    (s : List E) (hvK : IsInK value) (hN : kToNat (value.limb 0) < 2 ^ (n + 1))
    (hp : ∀ j < n + 1, LoadHolds rd p j (bitE ((kToNat (value.limb 0)).testBit j)))
    (hs : s.length = n + 1) (hrs : ReadsAt rd sq s) :
    ∃ τ : Val, τ (.n 0) = value ∧ τ (.n 1) = sq ∧ τ (.n 2) = word (2 ^ (n + 1)) 0 0 ∧
      τ (.n 3) = p ∧ Stmt.HoldsList C rd τ (gpwBody n) False (fun rs => rs =
        [gpwProd (fun j => bitE ((kToNat (value.limb 0)).testBit j)) (fun j => s.getD j 0) (n + 1)]) := by
    set N := kToNat (value.limb 0)
    set b := fun j => bitE (N.testBit j)
    set sv := fun j => s.getD j 0
    set τ := setl (setv (setl (Val.ofArgs [value, sq]) 2 [word (2 ^ (n + 1)) 0 0, p]) 4
      (12 * n + 8) (gpwVals b sv n)) (12 + 12 * n) [gpwProd b sv (n + 1)]
    have gv : ∀ i < 12 * n + 8, τ (.n (4 + i)) = gpwVals b sv n i := fun i hi => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
    have g0 : ∀ i < 8, τ (.n (4 + i)) = [b 0, b 0 * b 0, 1, sv 0, 1, sv 0 + 1, b 0 * (sv 0 + 1),
        1 + b 0 * (sv 0 + 1)].getD i 0 := fun i hi => by
      rw [gv i (by omega), gpwVals_zero _ _ _ _ hi]
    have gs : ∀ j c, j + 1 ≤ n → c < 12 → τ (.n (12 + 12 * j + c)) = [b (j + 1),
        b (j + 1) * b (j + 1), word (2 ^ (j + 1)) 0 0, b (j + 1) * word (2 ^ (j + 1)) 0 0,
        ∑ t ∈ Finset.range (j + 2), b t * coordBasis t, 1, sv (j + 1), 1, sv (j + 1) + 1,
        b (j + 1) * (sv (j + 1) + 1), 1 + b (j + 1) * (sv (j + 1) + 1), gpwProd b sv (j + 2)].getD
        c 0 := fun j c hj hc => by
      rw [show 12 + 12 * j + c = 4 + (8 + 12 * j + c) by omega, gv _ (by omega),
        gpwVals_succ _ _ _ _ _ hj hc]
    have hv : value = eOfNat N := by
      rw [eOfNat, ofBits_kToNat]; exact eq_ofK_limb hvK
    have hsv : ∀ j < n + 1, LoadHolds rd sq j (sv j) := fun j hj => by
      have := hrs j (by omega)
      simp only [sv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < s.length by omega),
        Option.getD_some]
      exact this
    have hacc : ∀ j < n + 1, τ (.n (gpwAcc j)) = ∑ t ∈ Finset.range (j + 1), b t * coordBasis t ∧
        τ (.n (gpwG j)) = gpwProd b sv (j + 1) := fun j hj => by
      cases j with
      | zero =>
        refine ⟨?_, ?_⟩
        · have := g0 0 (by omega)
          rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
            eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
          exact this
        · have := g0 7 (by omega)
          rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
          exact this
      | succ j =>
        rw [show gpwAcc (j + 1) = 12 + 12 * j + 4 by simp only [gpwAcc]; omega,
          show gpwG (j + 1) = 12 + 12 * j + 11 by simp only [gpwG]; omega]
        exact ⟨gs j 4 (by omega) (by omega), gs j 11 (by omega) (by omega)⟩
    refine ⟨τ, by simp only [τ]; b1_look, by simp only [τ]; b1_look, by simp only [τ]; b1_look,
      by simp only [τ]; b1_look, ?_⟩
    rw [gpwBody]
    simp only [holdsList_append, holdsList_range_flatten (n + 1) gpwBlk (fun j => by cases j <;> rfl),
      holds_gpwBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
    refine ⟨by simp only [τ]; b1_look, fun j hj => ?_, ?_, ?_, ?_⟩
    · cases j with
      | zero =>
        have e4 := g0 0 (by omega); have e5 := g0 1 (by omega); have e6 := g0 2 (by omega)
        have e7 := g0 3 (by omega); have e8 := g0 4 (by omega); have e9 := g0 5 (by omega)
        have e10 := g0 6 (by omega); have e11 := g0 7 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
          at e4 e5 e6 e7 e8 e9 e10 e11
        have t3 : τ (.n 3) = p := by simp only [τ]; b1_look
        have t1 : τ (.n 1) = sq := by simp only [τ]; b1_look
        refine ⟨?_, by rw [e5, e4], by rw [e5, e4, bitE_mul_self]; exact e_add_self _, e6, ?_, e8,
          by rw [e9, e7, e8], by rw [e10, e4, e9], by rw [e11, e6, e10]⟩
        · rw [t3, e4]; exact hp 0 (by omega)
        · rw [t1, e7]; exact hsv 0 (by omega)
      | succ j =>
        have e := fun c (hc : c < 12) => gs j c (by omega) hc
        have f0 := e 0 (by omega); have f1 := e 1 (by omega); have f2 := e 2 (by omega)
        have f3 := e 3 (by omega); have f4 := e 4 (by omega); have f5 := e 5 (by omega)
        have f6 := e 6 (by omega); have f7 := e 7 (by omega); have f8 := e 8 (by omega)
        have f9 := e 9 (by omega); have f10 := e 10 (by omega); have f11 := e 11 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ,
          show ∀ k, 12 + 12 * j + k = k + 12 + 12 * j from fun k => by ring]
          at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
        have t3 : τ (.n 3) = p := by simp only [τ]; b1_look
        have t1 : τ (.n 1) = sq := by simp only [τ]; b1_look
        obtain ⟨ha, hg⟩ := hacc j (by omega)
        refine ⟨?_, by rw [f1, f0], ?_, f2, by rw [f3, f0, f2], ?_, f5, ?_, f7, by rw [f8, f6, f7],
          by rw [f9, f0, f8], by rw [f10, f5, f9], ?_⟩
        · rw [t3, f0]; exact hp (j + 1) hj
        · rw [f1, f0]; simp only [b, bitE_mul_self]; exact e_add_self _
        · rw [f4, ha, f3, Finset.sum_range_succ (n := j + 1), word_coordBasis (by omega)]
        · rw [t1, f6]; exact hsv (j + 1) hj
        · rw [f11, hg, f10, gpwProd, gpwProd, Finset.prod_range_succ (n := j + 1)]
    · obtain ⟨ha, -⟩ := hacc n (by omega)
      have hr := reconstruct_bits 0 hN
      simp only [Nat.zero_add, pow_zero, one_mul] at hr
      have t0 : τ (.n 0) = value := by simp only [τ]; b1_look
      rw [ha, t0, hr, eOfNat192_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide)
        (by omega))), ← hv]
      exact e_add_self _
    · obtain ⟨-, hg⟩ := hacc n (by omega)
      rw [hg]
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega), Nat.sub_self]
      rfl
    · simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega), Nat.sub_self]
      rfl

/-- `g_power_of_word__L6`'s statements before its return. -/
def gpwPre : List Stmt := (gpwBody 5).take ((gpwBody 5).length - 1)

theorem gpwBody_eq : gpwBody 5 = gpwPre ++ [.ret [.n 72]] := stmtsEqb_sound (by decide +kernel)

theorem gpwPre_straight : gpwPre.all Main.Stmt.straight = true := by decide +kernel

theorem gpwPre_allocs : gpwPre.filterMap Main.Stmt.allocSz = [(.n 3, .inr (.n 2))] := by
  decide +kernel

theorem gpwPre_addrs : gpwPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem gpwPre_calls : gpwPre.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem gpwPre_loads : gpwPre.filterMap Stmt.loadS =
    [(.n 3, 0), (.n 1, 0), (.n 3, 1), (.n 1, 1), (.n 3, 2), (.n 1, 2), (.n 3, 3), (.n 1, 3),
      (.n 3, 4), (.n 1, 4), (.n 3, 5), (.n 1, 5)] := by decide +kernel

theorem find_gpw6 : coreProgram.find? "g_power_of_word__L6" = some Data.core172 :=
  Program.find?_of_indexOf? (j := 172) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem gpw6_not_loop : coreProgram.loop "g_power_of_word__L6" = false := by
  rw [Program.loop_of_find? find_gpw6]; decide +kernel

/-- The bits of `N` and the squares' table words. -/
def gpwBits (N : ℕ) : List E := (List.range 6).map fun j => bitE (N.testBit j)

def gpwSq : List E := (List.range 6).map fun j => gen ^ 2 ^ j

theorem readsAt_map_range {rd : Reader} {p : E} {m : ℕ} {f : ℕ → E} (h : ReadsAt rd p ((List.range m).map f)) :
    ∀ j < m, LoadHolds rd p j (f j) := fun j hj => by
  have := h j (by simpa using hj); simpa using this

/-- **`g_power_of_word__L6`, placed**: on `E(N)`, `N < 64`, and the squares' words at `g^qb`, its
bit buffer its one `HeapBuf`. -/
theorem gpw6_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {N : ℕ} (hN : N < 64)
    (qb : ℕ) :
    CompleteAtB fs cert k "g_power_of_word__L6" [(qb, gpwSq)] [eOfNat N, ofK (Parameters.gpow qb)]
      (Returns [gpwProd (fun j => bitE (N.testBit j)) (fun j => gpwSq.getD j 0) 6])
      (fs "g_power_of_word__L6" + 6) := by
  refine completeAt_leafB find_gpw6 gpw6_not_loop k _ _ _ [6] (fun _ => [gpwBits N])
    (fun _ => by simp [gpwBits]) fun fp rd _ hL hLin => ?_
  have hk : kToNat ((eOfNat N).limb 0) = N := kToNat_eOfNat_limb0 (by omega)
  simp only [bufL, bases, List.zip_cons_cons, List.zip_nil_right, Main.memL_cons, Main.memL_nil,
    and_true] at hL hLin
  obtain ⟨τ, t0, t1, t2, t3, hh⟩ := gpw_holds_at (C := coreProgram.Rel rd) 5 (by decide) rd
    (eOfNat N) (ofK (Parameters.gpow qb)) (ofK (Parameters.gpow (fp + fs "g_power_of_word__L6")))
    gpwSq (eOfNat_isInK N) (by rw [hk]; exact hN)
    (fun j hj => by rw [hk]; exact readsAt_map_range hL j hj) (by simp [gpwSq]) hLin
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core172) = true :=
    coreProgram_wf Data.core172 (List.mem_of_find?_eq_some find_gpw6)
  rw [core172_body, gpwBody_eq] at hwf
  rw [gpwBody_eq] at hh
  have hw := Main.walk_straight τ [.n 72] gpwPre gpwPre_straight
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ gpwPre gpwPre_straight
  rw [gpwPre_allocs] at e1 e2
  rw [gpwPre_addrs] at e3
  rw [gpwPre_calls] at e4
  have hs := walk_sat _ hwf hh
  rw [hw] at hs
  have h6 : logG (τ (.n 2)) = 6 := by
    rw [t2, word_two_pow (a := 6) (by decide), gen_pow_eq_ofK]; exact logG_spec (by decide)
  refine ⟨τ, _, _, by rw [show Fn.params Data.core172 = [.n 0, .n 1] from rfl]; simp [t0, t1],
    by rw [core172_body, gpwBody_eq]; exact hw, by rw [hs.2, hk], fun e he => (hs.1 e he).1, e4,
    by rw [e3], by rw [e2]; simp [h6], by rw [e1]; simp [t3, bases], fun A hA => ?_⟩
  rw [loadAddrs_straight τ gpwPre gpwPre_straight, gpwPre_loads] at hA
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false, t1, t3,
    Main.addr_ofK] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, Or.inl ⟨(fp + fs "g_power_of_word__L6", gpwBits N), by simp [bufL, bases],
      by simp, by simp [gpwBits]⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨(qb, gpwSq), by simp, by simp, by simp [gpwSq]⟩⟩
  · exact ⟨_, rfl, Or.inl ⟨(fp + fs "g_power_of_word__L6", gpwBits N), by simp [bufL, bases],
      by simp, by simp [gpwBits]⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨(qb, gpwSq), by simp, by simp, by simp [gpwSq]⟩⟩
  · exact ⟨_, rfl, Or.inl ⟨(fp + fs "g_power_of_word__L6", gpwBits N), by simp [bufL, bases],
      by simp, by simp [gpwBits]⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨(qb, gpwSq), by simp, by simp, by simp [gpwSq]⟩⟩
  · exact ⟨_, rfl, Or.inl ⟨(fp + fs "g_power_of_word__L6", gpwBits N), by simp [bufL, bases],
      by simp, by simp [gpwBits]⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨(qb, gpwSq), by simp, by simp, by simp [gpwSq]⟩⟩
  · exact ⟨_, rfl, Or.inl ⟨(fp + fs "g_power_of_word__L6", gpwBits N), by simp [bufL, bases],
      by simp, by simp [gpwBits]⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨(qb, gpwSq), by simp, by simp, by simp [gpwSq]⟩⟩
  · exact ⟨_, rfl, Or.inl ⟨(fp + fs "g_power_of_word__L6", gpwBits N), by simp [bufL, bases],
      by simp, by simp [gpwBits]⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨(qb, gpwSq), by simp, by simp, by simp [gpwSq]⟩⟩

end
end LeanVM.Guest.B1.VerifySub
