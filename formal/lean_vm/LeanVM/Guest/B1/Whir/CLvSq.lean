/-
  LeanVM.Guest.B1.Whir.CLvSq

  A level's query grind and squeezes honestly on f128: the grind's check, the squeeze run, the
  first word decoded, the squeeze loop entered, the last capacity loaded.
-/

module

public import LeanVM.Guest.B1.Whir.CLvCommit
public import LeanVM.Guest.B1.Whir.CAtoms
public import LeanVM.Guest.B1.Place.OsCallV

/-!
# A level's squeezes, honestly (G:1594-1620)

* `call0_blk`: a call returning nothing, holding where its relation does.
* `osSqueezes_complete`: the squeeze run allocated at a given pointer, the carried capacity stored
  in its row `1`, the first query word decoded, the squeeze loop entered at `g`, `g^S`, the
  capacity after `S - 1` squeezes loaded from row `S`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The capacity after `n` squeezes from `cap`. -/
def sqCap (cap : List E) (n : ℕ) : List E := ((⟨cap, []⟩ : Fs).squeezeN n).2.cap

theorem sqCap_length {cap : List E} (h : cap.length = 5) (n : ℕ) : (sqCap cap n).length = 5 :=
  squeezeN_cap_length n _ h

/-- The values of the squeeze loop's entry. -/
def sqEntryVals (S : ℕ) : List E := [gw 1, gw S, gw 1 + gw S, gw 1, gw S]

/-- The values of the last capacity's loads: its row's pointer, the capacity `capS`. -/
def sqTailVals (S : ℕ) (sqz : E) (capS : List E) : List E :=
  [gw (S * 5), sqz * gw (S * 5)] ++ capS

/-- **A level's squeezes, honestly** (G:1594-1620). -/
theorem osSqueezes_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hw0 : st.word0 < st.k) (pZ : E)
    (hpo : lv.posOff < u128Bound) (hS5 : lv.squeezes * 5 < u128Bound) (hS : lv.squeezes < u128Bound)
    (hrows : ∀ C rd, H C rd → (∀ i < 5, LoadHolds rd pZ (5 + i) ((st.fsv σ).getD i 0)) ∧
      ∀ i < 5, LoadHolds rd pZ (lv.squeezes * 5 + i) ((sqCap (st.fsv σ) (lv.squeezes - 1)).getD i 0))
    (hdec : ∀ C rd, H C rd → C ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      [σ (.n st.word0), σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] [])
    (hloop : ∀ C rd, H C rd → gen + gen ^ lv.squeezes ≠ 0 → C (c.sqLoop lvl)
      [gen, gen ^ lv.squeezes, pZ, σ (.n osQpos), σ (.n osQbp), σ (.n osTabs)] []) :
    BlkA H σ st.k (osSqueezes c lvl lv st).2.k (osSqueezes c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osSqueezes c lvl lv st).2 ∧
      (osSqueezes c lvl lv st).2.F σ' = ⟨sqCap (st.fsv σ) (lv.squeezes - 1), []⟩ ∧
      σ' (.n st.k) = gw ((c.maxSq + 1) * 5) ∧ σ' (.n (st.k + 1)) = pZ ∧
      (osSqueezes c lvl lv st).2.cur σ' = st.cur σ ∧
      (osSqueezes c lvl lv st).2.claim = st.claim ∧ (osSqueezes c lvl lv st).2.pad = st.pad ∧
      (osSqueezes c lvl lv st).2.co = st.co ∧ (osSqueezes c lvl lv st).2.cb = st.cb ∧
      (osDecCallAt c lv st).2.2.1.map σ' = [σ (.n st.word0), σ (.n osQpos) * gen ^ lv.posOff,
        σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osSqCallAt c lvl lv st).1.map σ' = some (gen + gen ^ lv.squeezes) ∧
      (osSqCallAt c lvl lv st).2.2.1.map σ' =
        [gen, gen ^ lv.squeezes, pZ, σ (.n osQpos), σ (.n osQbp), σ (.n osTabs)]) := by
  set k := st.k with hk
  set cap := st.fsv σ with hcap
  set S := lv.squeezes with hSd
  set s0 : OsSt := { st with k := k + 2 } with hs0
  set qp := osMatS c.plan osQpos lv.posOff s0 with hqp
  set wp := osMatS c.plan osQbp lv.posOff qp.2.2 with hwp
  set l := wp.2.2.k with hl
  have k36 : 36 ≤ k := hsf.k
  have kq : k + 2 ≤ qp.2.2.k := osMatS_k c.plan osQpos lv.posOff s0
  have kw : qp.2.2.k ≤ l := osMatS_k c.plan osQbp lv.posOff qp.2.2
  have pqp : qp.2.1 < qp.2.2.k := osMatS_ptr_lt _ _ _ _ (show 33 < k + 2 by omega)
  have pwp : wp.2.1 < l := osMatS_ptr_lt _ _ _ _ (show 35 < qp.2.2.k by omega)
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hsf.fs
  have hfb : ∀ f ∈ st.fs, f < k := hsf.below.fs
  have hmb0 : MatsBelow s0.k s0.mats := show MatsBelow (k + 2) st.mats from fun m hm ↦ by
    obtain ⟨a, b, d⟩ := hsf.below.mats m hm; exact ⟨by omega, by omega, by omega⟩
  -- the heap and the row
  have b1 := BlkA.seq (H := H) (show k ≤ k + 2 by omega) (show k + 2 ≤ k + 2 from le_rfl)
    (heap_blk σ ((c.maxSq + 1) * 5) k pZ)
    (B := st.fs.zipIdx.map fun (f, i) ↦ osLd f (k + 1) (5 + i)) (OutB := fun _ ↦ True) fun σ1 ha1 ho1 ↦
      stores_blk fun C rd hH σ' ha ↦ by
        obtain ⟨-, e1⟩ := ho1 C rd hH
        have ep : σ' (.n (k + 1)) = pZ := by rw [ha _ (by omega), e1]
        have hr := (hrows C rd hH).1
        have v : ∀ f ∈ st.fs, σ' (.n f) = σ (.n f) := fun f hf' ↦ by
          rw [ha _ (by have := hfb f hf'; omega), ha1 _ (hfb f hf')]
        have hc : cap = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
          simp [hcap, OsSt.fsv, hf]
        rw [hc] at hr
        rw [hf] at v ⊢
        simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons,
          allOk_nil, and_true, stmtOk_atom, holds_load, osLd, ep, Nat.zero_add, Nat.reduceAdd]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v
        rw [v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2]
        exact ⟨hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hr 3 (by omega), hr 4 (by omega)⟩
  -- the pointers
  have b2 := BlkA.seq (H := H) (show k ≤ k + 2 by omega) kq b1 (B := qp.1)
    (OutB := fun σ' ↦ σ' (.n qp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ' qp.2.2.mats ∧
      MatsBelow qp.2.2.k qp.2.2.mats) fun σ1 ha1 _ ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQpos) (off := lv.posOff) (s := s0) σ1
        (show 33 < k + 2 by omega) hmb0 (fun C rd hH ↦
          matsOk_agree (hok C rd hH).mats hsf.below.mats fun i hi ↦ ha1 i hi) hpo
      rw [ha1 osQpos (by show 33 < k; omega)] at h
      exact h
  have b3 := BlkA.seq (H := H) (show k ≤ qp.2.2.k by omega) kw b2 (B := wp.1)
    (OutB := fun σ' ↦ σ' (.n wp.2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧ MatsOk σ' wp.2.2.mats ∧
      MatsBelow wp.2.2.k wp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQbp) (off := lv.posOff) (s := qp.2.2) σ1
        (show 35 < qp.2.2.k by omega) (osMatS_below hmb0 (show 33 < k + 2 by omega))
        (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hpo
      rw [ha1 osQbp (by show 35 < k; omega)] at h
      exact h
  -- the first word decoded
  have b4 := BlkA.seq (H := H) (show k ≤ l by omega) (show l ≤ l from le_rfl) b3
    (B := [.call ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
      ([st.word0, qp.2.1, wp.2.1, osTabs].map V.n) []])
    (OutB := fun σ' ↦ ([st.word0, qp.2.1, wp.2.1, osTabs].map V.n).map σ' =
      [σ (.n st.word0), σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff,
        σ (.n osTabs)]) fun σ1 ha1 ho1 ↦ by
      have h := call0_blk (H := H) (σ := σ1) (k := l)
        (f := "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        (args := [st.word0, qp.2.1, wp.2.1, osTabs]) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl
          · omega
          · omega
          · omega
          · show 9 < l; omega) fun C rd hH ↦ by
        obtain ⟨⟨-, e2, -⟩, e3, -⟩ := ho1 C rd hH
        simp only [List.map_cons, List.map_nil]
        rw [e2, e3, ha1 _ hw0, ha1 _ (show 9 < k by omega)]
        exact hdec C rd hH
      refine h.monoH fun C rd hH σ' ha e ↦ ?_
      obtain ⟨⟨-, e2, -⟩, e3, -⟩ := ho1 C rd hH
      rw [e]
      simp only [List.map_cons, List.map_nil]
      rw [e2, e3, ha1 _ hw0, ha1 _ (show 9 < k by omega)]
  have g1 : gw 1 = gen := by rw [gw_eq (by unfold u128Bound; omega), pow_one]
  have gS : gw S = gen ^ S := gw_eq hS
  -- the loop's entry
  have b5 := BlkA.seq (H := H) (show k ≤ l by omega) (show l ≤ l + 5 by omega) b4
    (B := osLoopCall (c.sqLoop lvl) 1 S [k + 1, osQpos, osQbp, osTabs] l)
    (OutB := fun σ' ↦ σ' (.n (l + 2)) = gen + gen ^ S ∧ σ' (.n (l + 3)) = gen ∧
      σ' (.n (l + 4)) = gen ^ S) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF l (sqEntryVals S), fun C rd hH σ' ha hr ↦ ?_⟩
      have v : ∀ j < 5, σ' (.n (l + j)) = (sqEntryVals S).getD j 0 := fun j hj ↦
        lstF_at hr (by simp [sqEntryVals]) j (by simp [sqEntryVals]; omega)
      have v0 := v 0 (by omega)
      have v1 := v 1 (by omega)
      have v2 := v 2 (by omega)
      have v3 := v 3 (by omega)
      have v4 := v 4 (by omega)
      simp only [sqEntryVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, g1,
        gS] at v0 v1 v2 v3 v4
      refine ⟨?_, v2, v3, v4⟩
      have e1 := (ho1 C rd hH).1.1.1.1.2
      have ep : σ' (.n (k + 1)) = pZ := by rw [ha _ (show k + 1 < l by omega), e1]
      simp only [osLoopCall, allOk_cons, allOk_nil, and_true, holds_const, holds_add, StmtOk,
        osCst, osAdd, List.map_cons, List.map_nil, v0, v1, v2, v3, v4, g1, gS, ep]
      refine ⟨trivial, trivial, trivial, trivial, trivial,
        isInK_add (by simpa using gen_pow_isInK 1) (gen_pow_isInK S), fun hne ↦ ?_⟩
      rw [ha _ (show 33 < l by omega), ha _ (show 35 < l by omega), ha _ (show 9 < l by omega),
        ha1 _ (show 33 < k by omega), ha1 _ (show 35 < k by omega), ha1 _ (show 9 < k by omega)]
      exact hloop C rd hH hne
  -- the last capacity
  have hS1 : S * 5 < u128Bound := hS5
  have b6 := BlkA.seq (H := H) (show k ≤ l + 5 by omega) (show l + 5 ≤ l + 5 + 7 by omega) b5
    (B := [osCst (l + 5) (gw (S * 5)), osMul (l + 5 + 1) (k + 1) (l + 5)] ++
      ((List.range 5).map fun i ↦ osLd (l + 5 + 2 + i) (l + 5 + 1) i))
    (OutB := fun σ' ↦ ∀ j < 7, σ' (.n (l + 5 + j)) = (sqTailVals S pZ (sqCap cap (S - 1))).getD j 0)
    fun σ1 ha1 ho1 ↦ by
      have hcl : (sqCap cap (S - 1)).length = 5 := sqCap_length (by simp [hcap, OsSt.fsv, hsf.fs]) _
      refine ⟨lstF (l + 5) (sqTailVals S pZ (sqCap cap (S - 1))), fun C rd hH σ' ha hr ↦ ?_⟩
      have v : ∀ j < 7, σ' (.n (l + 5 + j)) = (sqTailVals S pZ (sqCap cap (S - 1))).getD j 0 :=
        fun j hj ↦ lstF_at hr (by simp [sqTailVals, hcl]) j (by simp [sqTailVals, hcl]; omega)
      refine ⟨?_, v⟩
      have e1 := (ho1 C rd hH).1.1.1.1.1.2
      have ep : σ' (.n (k + 1)) = pZ := by rw [ha _ (show k + 1 < l + 5 by omega), e1]
      have hr2 := (hrows C rd hH).2
      have w : ∀ j, 2 ≤ j → j < 7 → σ' (.n (l + 5 + j)) = (sqCap cap (S - 1)).getD (j - 2) 0 :=
        fun j h1 h2 ↦ by
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
          rw [v _ h2]
          simp only [sqTailVals, List.cons_append, List.nil_append, List.getD_cons_succ,
            Nat.add_sub_cancel]
      simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_mul,
        holds_load, osCst, osMul, osLd, Nat.add_assoc, Nat.reduceAdd]
      have v0 := v 0 (by omega)
      have v1 := v 1 (by omega)
      simp only [sqTailVals, List.getD_cons_zero, List.getD_cons_succ, List.cons_append,
        Nat.add_zero] at v0 v1
      have u0 : σ' (.n (l + 5)) = gw (S * 5) := by simpa using v0
      have u1 : σ' (.n (l + 6)) = pZ * gw (S * 5) := by simpa using v1
      have ld : ∀ i < 5, LoadHolds rd (σ' (.n (l + 6))) i (σ' (.n (l + 5 + (i + 2)))) := fun i hi ↦ by
        rw [u1, w (i + 2) (by omega) (by omega), Nat.add_sub_cancel, gw_eq hS1, loadHolds_mul_gen_pow]
        exact hr2 i hi
      refine ⟨u0, by rw [u1, ep, u0], ld 0 (by omega), ld 1 (by omega), ld 2 (by omega),
        ld 3 (by omega), ld 4 (by omega)⟩
  have ek : (osSqueezes c lvl lv st).2.k = l + 5 + 7 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b6.agree fun C rd hH σ' ha ⟨ho, hag⟩ ↦ ?_) (by
    simp only [osSqueezes, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨⟨⟨⟨eh0, eh1⟩, -⟩, -⟩, -, hmw, hbw⟩, edec⟩, el2, el3, el4⟩, e6⟩ := ho
  have hok' := hok C rd hH
  have hcl : (sqCap cap (S - 1)).length = 5 := sqCap_length (by simp [hcap, OsSt.fsv, hsf.fs]) _
  have w : ∀ j, j < 5 → σ' (.n (l + 5 + (j + 2))) = (sqCap cap (S - 1)).getD j 0 := fun j hj ↦ by
    rw [e6 _ (by omega)]
    simp only [sqTailVals, List.cons_append, List.nil_append, List.getD_cons_succ]
  have hb : MatsBelow wp.2.2.k wp.2.2.mats := hbw
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, hsf.co, fun p hp ↦ by have := hsf.padB p hp; omega,
    by omega⟩, hmw, ?_⟩, by omega, hag⟩, ?_, eh0, eh1, ?_, rfl, rfl, rfl, rfl, edec, ?_, ?_⟩
  · intro f hf
    have hf' : f ∈ [l + 5 + 2, l + 5 + 3, l + 5 + 4, l + 5 + 5, l + 5 + 6] := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show st.cb < l + 5 + 7; have := hsf.below.cb; omega
  · show st.claim < l + 5 + 7; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b, d⟩ := hb m hm
    exact ⟨by have : m.out < l := a; omega, by have : m.src < l := b; omega,
      by have : m.base < l := d; omega⟩
  · intro p hp
    have hb' := hsf.padB p hp
    obtain ⟨z1, z2, z3, z4⟩ := hok'.pad p hp
    rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  · show (⟨[l + 5 + 2, l + 5 + 3, l + 5 + 4, l + 5 + 5, l + 5 + 6].map (fun i ↦ σ' (.n i)), []⟩ :
      Fs) = _
    rw [five_getD hcl]
    simp only [List.map_cons, List.map_nil]
    rw [show l + 5 + 2 = l + 5 + (0 + 2) from rfl, w 0 (by omega), show l + 5 + 3 = l + 5 + (1 + 2) from rfl,
      w 1 (by omega), show l + 5 + 4 = l + 5 + (2 + 2) from rfl, w 2 (by omega),
      show l + 5 + 5 = l + 5 + (3 + 2) from rfl, w 3 (by omega), show l + 5 + 6 = l + 5 + (4 + 2) from rfl,
      w 4 (by omega)]
  · show σ' (.n st.cb) * gen ^ st.co = σ (.n st.cb) * gen ^ st.co
    rw [hag _ hsf.below.cb]
  · show some (σ' (.n (l + 2))) = _; rw [el2]
  · show [σ' (.n (l + 3)), σ' (.n (l + 4)), σ' (.n (k + 1)), σ' (.n osQpos), σ' (.n osQbp),
      σ' (.n osTabs)] = _
    rw [el3, el4, eh1, hag _ (show 33 < k by omega), hag _ (show 35 < k by omega),
      hag _ (show 9 < k by omega)]
end
end LeanVM.Guest.B1.Whir
