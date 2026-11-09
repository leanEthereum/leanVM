/-
  LeanVM.Guest.B1.Whir.CSqueezes

  A level's squeezes, honestly: the query positions' loop and the batching challenge.
-/

module

public import LeanVM.Guest.B1.Whir.CSqLoop

/-!
# The squeezes, honestly

`osSqueezes_complete`: from the carried capacity (nothing waiting), the squeeze run's rows
holding the squeeze chain (`SqNextMem`; the loop's own facts, `SqIterMem`, by
`sqLoop_complete`), the batching challenge the chain's next squeeze, its capacity carried
(`SqzOut`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The squeeze run's row `x` holds the capacity after the squeeze. -/
def SqNextMem (rd : Reader) (sqz x : E) (cap : List E) : Prop :=
  ∀ i < 5, LoadHolds rd (sqz * x ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0)

/-- What a level's squeezes leave: the challenge's capacity carried, the challenge, the zero
run allocated. -/
structure SqzOut (σ : Val) (st st' : OsSt) (F : Fs) : Prop where
  fsv : st'.fsv σ = F.squeeze.2.cap
  lam : σ (.n (st'.k - 1)) = F.squeeze.1
  pad : PadOk σ st'.pad
  padSome : ∃ p, st'.pad = some p ∧ p + 4 < st'.k
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ)
  below : st'.Below
  cb : st'.cb = st.cb
  co : st'.co = st.co
  w0 : st'.w0 = st.w0
  w1 : st'.w1 = st.w1
  k : st.k ≤ st'.k

/-- The zero run's values a level allocates: five at the first use, none after. -/
def padLenOf (st : OsSt) : ℕ := if st.pad = none then 5 else 0

/-- The squeezes' values, by segments. -/
def sqzSegs (c : OsCfg) (lv : OsLv) (st : OsSt) (sqz : E) (F : Fs) : List (ℕ × (ℕ → E)) :=
  let S := (F.squeezeN lv.squeezes).2.perm
  [(1, fun _ ↦ gw ((c.maxSq + 1) * 5)), (1, fun _ ↦ sqz),
    (5, fun i ↦ [word 1 0 0, gw lv.squeezes, word 1 0 0 + gw lv.squeezes, word 1 0 0,
      gw lv.squeezes].getD i 0),
    (1, fun _ ↦ gw (lv.squeezes * 5)), (1, fun _ ↦ sqz * gw (lv.squeezes * 5)),
    (5, fun i ↦ (F.squeezeN lv.squeezes).2.cap.getD i 0),
    (padLenOf st, fun i ↦ [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
      word 0 0 0].getD i 0),
    (13, cells13F S), (7, challengeVals (cells13F S 0) (cells13F S 1))]

theorem osSqueezes_completeC {C : CallRel} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hn0 : 0 < lv.squeezes) (hn5 : lv.squeezes * 5 < u128Bound)
    (hfs : st.fs.length = 5) (hb : st.Below) (hk : 164 ≤ st.k) (hcan : AllCanonical (st.fsv σ))
    (hpad : PadOk σ st.pad) (hpk : ∀ p, st.pad = some p → p + 4 < st.k)
    (sqz : E) (h0 : ∀ i < 5, LoadHolds rd sqz i ((st.fsv σ).getD i 0))
    (hm : ∀ j < lv.squeezes, SqNextMem rd sqz (gen ^ j) ((⟨st.fsv σ, []⟩ : Fs).squeezeN j).2.cap)
    (hL : IsInK (1 + gen ^ lv.squeezes) ∧ (1 + gen ^ lv.squeezes ≠ 0 →
      C (c.sqLoop lvl) [1, gen ^ lv.squeezes, sqz, σ (.n osQpos), σ (.n osQbp), σ (.n osWin)] [])) :
    BlkF C rd σ st.k (osSqueezes c lvl lv st).2.k
      (fun i ↦ segLookup (sqzSegs c lv st sqz ⟨st.fsv σ, []⟩) (i - st.k)) (osSqueezes c lvl lv st).1
      (fun σ' ↦ SqzOut σ' st (osSqueezes c lvl lv st).2
        ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 ∧ AgreeBelow st.k σ σ') := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  set n := lv.squeezes with hn
  set F0 : Fs := ⟨st.fsv σ, []⟩ with hF0
  set Fn := (F0.squeezeN n).2 with hFn
  have hFnp : Fn = ⟨Fn.cap, []⟩ := fs_of_pend_nil (squeezeN_pend rfl _)
  set S := Fn.perm with hS
  set segs := sqzSegs c lv st sqz F0 with hsegs
  set padLen := padLenOf st with hpl
  have hlen : segLen segs = 34 + padLen := by
    simp only [hsegs, sqzSegs, segLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← hpl]
    omega
  have hpd : (osPad st.pad (st.k + 14)).2.2 = st.k + 14 + padLen := by
    rw [hpl, padLenOf]; cases st.pad <;> rfl
  have hk' : (osSqueezes c lvl lv st).2.k = st.k + 14 + padLen + 20 := by
    show (osPad st.pad (st.k + 14)).2.2 + 20 = _; rw [hpd]
  intro σ' ha hv
  have HV : ∀ j < segLen segs, σ' (.n (st.k + j)) = segLookup segs j := fun j hj ↦ by
    rw [hv _ (by omega) (by rw [hk']; omega)]
    show segLookup segs (st.k + j - st.k) = _
    rw [Nat.add_sub_cancel_left]
  have sv := seg_val HV
  have hagree : ∀ i < st.k, σ' (.n i) = σ (.n i) := ha
  have hfl : ∀ f ∈ st.fs, f < st.k := hb.fs
  rw [hf] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  have hfsv : st.fsv σ = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [OsSt.fsv, hf]
  set k := st.k with hkdef
  have hL9 : segs.length = 9 := by simp [hsegs, sqzSegs]
  have v0 : σ' (.n k) = gw ((c.maxSq + 1) * 5) := by
    have := sv 0 (by omega) 0 (by simp [hsegs, segLen]) 0 (by simp [hsegs, sqzSegs])
    simpa [hsegs, sqzSegs] using this
  have v1 : σ' (.n (k + 1)) = sqz := by
    have := sv 1 (by omega) 1 (by simp [hsegs, segLen, sqzSegs]) 0 (by simp [hsegs, sqzSegs])
    simpa [hsegs, sqzSegs] using this
  have vl : ∀ i < 5, σ' (.n (k + 2 + i)) = [word 1 0 0, gw n, word 1 0 0 + gw n, word 1 0 0,
      gw n].getD i 0 := fun i hi ↦ by
    have := sv 2 (by omega) 2 (by simp [hsegs, segLen, sqzSegs]) i (by simp [hsegs, sqzSegs]; omega)
    simpa [hsegs, sqzSegs] using this
  have v7 : σ' (.n (k + 7)) = gw (n * 5) := by
    have := sv 3 (by omega) 7 (by simp [hsegs, segLen, sqzSegs]) 0 (by simp [hsegs, sqzSegs])
    simpa [hsegs, sqzSegs] using this
  have v8 : σ' (.n (k + 8)) = sqz * gw (n * 5) := by
    have := sv 4 (by omega) 8 (by simp [hsegs, segLen, sqzSegs]) 0 (by simp [hsegs, sqzSegs])
    simpa [hsegs, sqzSegs] using this
  have vc : ∀ i < 5, σ' (.n (k + 9 + i)) = Fn.cap.getD i 0 := fun i hi ↦ by
    have := sv 5 (by omega) 9 (by simp [hsegs, segLen, sqzSegs]) i (by simp [hsegs, sqzSegs]; omega)
    simpa [hsegs, sqzSegs] using this
  have vp : ∀ i < padLen, σ' (.n (k + 14 + i)) = [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
      word 0 0 0].getD i 0 := fun i hi ↦ by
    have := sv 6 (by omega) 14 (by simp [hsegs, segLen, sqzSegs]) i (by simp [hsegs, sqzSegs, ← hpl]; omega)
    simpa [hsegs, sqzSegs] using this
  have vk : ∀ c < 13, σ' (.n (k + (14 + padLen) + c)) = cells13F S c := fun c hc ↦ by
    have := sv 7 (by omega) (14 + padLen) (by simp [hsegs, segLen, sqzSegs, ← hpl]; omega) c
      (by simp [hsegs, sqzSegs]; omega)
    simpa [hsegs, sqzSegs] using this
  have vch : ∀ i < 7, σ' (.n (k + (14 + padLen) + 13 + i)) =
      challengeVals (cells13F S 0) (cells13F S 1) i := fun i hi ↦ by
    have := sv 8 (by omega) (27 + padLen) (by simp [hsegs, segLen, sqzSegs, ← hpl]; omega) i
      (by simp [hsegs, sqzSegs]; omega)
    rw [show k + (14 + padLen) + 13 + i = k + (27 + padLen) + i by ring]
    simpa [hsegs, sqzSegs] using this
  have hgn : gw n = gen ^ n := gw_eq (by omega)
  have hgn5 : gw (n * 5) = gen ^ (5 * n) := by rw [gw_eq hn5, Nat.mul_comm]
  -- the last capacity, from the last iteration's row
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hlast : ∀ i < 5, LoadHolds rd (sqz * gen ^ (5 * n)) i (Fn.cap.getD i 0) := fun i hi ↦ by
    have hnx := hm n' (by omega) i hi
    have hsn : Fn = ((F0.squeezeN n').2).squeeze.2 := by rw [hFn, hn', squeezeN_snoc]
    have hpn : (F0.squeezeN n').2 = ⟨(F0.squeezeN n').2.cap, []⟩ :=
      fs_of_pend_nil (squeezeN_pend rfl _)
    rw [hsn, Fs.squeeze]
    rw [← hpn, ← pow_mul, loadHolds_mul_gen_pow] at hnx
    rw [loadHolds_mul_gen_pow, show 5 * n = n' * 5 + 5 by omega, Nat.add_assoc]
    exact hnx
  set pd := osPad st.pad (k + 14) with hpdd
  have hpz : PadOk σ' (some pd.2.1) ∧ AllOk C rd σ' pd.1 ∧ pd.2.1 + 4 < pd.2.2 + 20 := by
    rw [hpdd]
    cases hp : st.pad with
    | none =>
      have hpl5 : padLen = 5 := by rw [hpl, padLenOf, hp]; rfl
      have p0 := vp 0 (by omega); have p1 := vp 1 (by omega); have p2 := vp 2 (by omega)
      have p3 := vp 3 (by omega); have p4 := vp 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at p0 p1 p2 p3 p4
      refine ⟨⟨by simpa [osPad, word_zero] using p1, by simpa [osPad, word_zero] using p2,
        by simpa [osPad, word_zero] using p3, by simpa [osPad, word_zero] using p4⟩, ?_, by simp [osPad]⟩
      simp only [osPad, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨p0, by simpa using p1, by simpa using p2, by simpa using p3, by simpa using p4⟩
    | some p =>
      rw [hp] at hpad
      have hpk' := hpk p hp
      have := hkdef
      obtain ⟨z1, z2, z3, z4⟩ := hpad
      refine ⟨⟨show σ' (.n (p + 1)) = 0 by rw [hagree (p + 1) (by omega)]; exact z1,
        show σ' (.n (p + 2)) = 0 by rw [hagree (p + 2) (by omega)]; exact z2,
        show σ' (.n (p + 3)) = 0 by rw [hagree (p + 3) (by omega)]; exact z3,
        show σ' (.n (p + 4)) = 0 by rw [hagree (p + 4) (by omega)]; exact z4⟩, allOk_nil, ?_⟩
      simp [osPad]; omega
  -- the squeeze after the loop
  have hj : pd.2.2 = k + (14 + padLen) := by rw [hpdd, hpd]; ring
  have hcm : Fn.cap = [k + 9, k + 10, k + 11, k + 12, k + 13].map fun i ↦ σ' (.n i) := by
    have hcl : Fn.cap.length = 5 := squeezeN_cap_length _ _ (by simp [hF0, OsSt.fsv, hfs])
    obtain ⟨q0, q1, q2, q3, q4, hq⟩ : ∃ q0 q1 q2 q3 q4, Fn.cap = [q0, q1, q2, q3, q4] := by
      match h : Fn.cap, hcl with
      | [q0, q1, q2, q3, q4], _ => exact ⟨q0, q1, q2, q3, q4, rfl⟩
    have e0 := vc 0 (by omega); have e1 := vc 1 (by omega); have e2 := vc 2 (by omega)
    have e3 := vc 3 (by omega); have e4 := vc 4 (by omega)
    rw [hq] at e0 e1 e2 e3 e4
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.add_assoc,
      Nat.reduceAdd] at e0 e1 e2 e3 e4
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, hq]
  have hcanF : AllCanonical Fn.cap := squeezeN_cap_canonical _ _ (by rw [hF0]; exact hcan)
  have hSF : (⟨[k + 9, k + 10, k + 11, k + 12, k + 13].map fun i ↦ σ' (.n i), []⟩ : Fs).perm = S := by
    rw [← hcm, hS, ← hFnp]
  have hsq := osSqueeze0_complete (C := C) (rd := rd) (σ := σ') (p := pd.2.1)
    (cap := [k + 9, k + 10, k + 11, k + 12, k + 13]) (j := pd.2.2) rfl hpz.1
    (by rw [← hcm]; exact hcanF) (fun c hc ↦ by rw [hSF, hj]; exact vk c hc)
    (fun i hi ↦ by
      rw [hj, vch i hi]
      have e0 := vk 0 (by omega)
      rw [Nat.add_zero] at e0
      rw [e0, vk 1 (by omega)])
  rw [hSF] at hsq
  have hfsT : ([pd.2.2 + 8, pd.2.2 + 9, pd.2.2 + 10, pd.2.2 + 11, pd.2.2 + 12].map
      fun i ↦ σ' (.n i)) = Fn.squeeze.2.cap := by
    simp only [List.map_cons, List.map_nil, Fs.squeeze, capOf, hj]
    rw [vk 8 (by omega), vk 9 (by omega), vk 10 (by omega), vk 11 (by omega), vk 12 (by omega)]
    simp [cells13F, hS]
  have hcan' : AllCanonical ((osSqueezes c lvl lv st).2.fsv σ') := by
    show AllCanonical ([pd.2.2 + 8, pd.2.2 + 9, pd.2.2 + 10, pd.2.2 + 11, pd.2.2 + 12].map
      fun i ↦ σ' (.n i))
    rw [hfsT]; exact capOf_canonical _
  have hkk : k ≤ (osSqueezes c lvl lv st).2.k := by show k ≤ pd.2.2 + 20; omega
  refine ⟨?_, ⟨hfsT, ?_, hpz.1, ⟨pd.2.1, rfl, hpz.2.2⟩, rfl, hcan', ?_, rfl, rfl, rfl, rfl, hkk⟩,
    ha⟩
  · simp only [osSqueezes, allOk_append]
    rw [← hkdef]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hpz.2.1⟩, hsq.1⟩
    · simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact v0
    · rw [hf]
      simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons,
        allOk_nil, and_true, StmtOk, Atom.Holds, Nat.zero_add]
      rw [v1, hagree _ hfl.1, hagree _ hfl.2.1, hagree _ hfl.2.2.1, hagree _ hfl.2.2.2.1,
        hagree _ hfl.2.2.2.2]
      have := h0
      rw [hfsv] at this
      exact ⟨this 0 (by omega), this 1 (by omega), this 2 (by omega), this 3 (by omega),
        this 4 (by omega)⟩
    · simp only [osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
        List.map_nil]
      have l0 := vl 0 (by omega); have l1 := vl 1 (by omega); have l2 := vl 2 (by omega)
      have l3 := vl 3 (by omega); have l4 := vl 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at l0 l1 l2 l3 l4
      have hloop := hL
      have hqp : σ' (.n osQpos) = σ (.n osQpos) := hagree osQpos (by unfold osQpos; omega)
      have hqb : σ' (.n osQbp) = σ (.n osQbp) := hagree osQbp (by unfold osQbp; omega)
      have hqw : σ' (.n osWin) = σ (.n osWin) := hagree osWin (by unfold osWin; omega)
      refine ⟨l0, l1, by rw [l2, l0, l1], l3, l4, by rw [l2, word_one, hgn]; exact hloop.1,
        fun h ↦ ?_⟩
      rw [l3, l4, v1, hqp, hqb, hqw, word_one, hgn]
      rw [l2, word_one, hgn] at h
      exact hloop.2 h
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨v7, by rw [v8, v1, v7]⟩
    · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, Nat.add_zero]
      rw [v8, hgn5]
      exact ⟨by have := vc 0 (by omega); rw [Nat.add_zero] at this; rw [this]
                exact hlast 0 (by omega),
        by have := vc 1 (by omega); rw [this]; exact hlast 1 (by omega),
        by have := vc 2 (by omega); rw [this]; exact hlast 2 (by omega),
        by have := vc 3 (by omega); rw [this]; exact hlast 3 (by omega),
        by have := vc 4 (by omega); rw [this]; exact hlast 4 (by omega)⟩
  · show σ' (.n (pd.2.2 + 20 - 1)) = _
    rw [show pd.2.2 + 20 - 1 = pd.2.2 + 19 by omega, hsq.2]
    rfl
  · have := hb.w0; have := hb.w1; have := hb.c; have := hb.b; have := hb.a; have := hb.t
    have := hb.cb
    refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [osSqueezes] at *
    all_goals omega

end
end LeanVM.Guest.B1.Whir
