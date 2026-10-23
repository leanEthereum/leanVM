/-
  LeanVM.Guest.B1.Tables.VtSortC

  `verify_tables`'s certified block order completes on the honest order (`VtSortComplete`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCIface
public import LeanVM.Guest.B1.Tables.FlockCAll

/-!
# The certified block order, complete

Each rank's values are its block `g^b`, the range checks' auxiliary words (`rcLow`, read from
the memory defined below `2^7`), the side word, its size `g^κ`, the offset stored and the next
one (`vt_c_rank0`, `vt_c_rankN`); a side is its ranks in `stackOrder`'s order, so the sizes do
not increase and ties ascend (`stackOrder_adj`), and the offsets are `stackOffsets`'s.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- The words a side's ranks read through: the order, the sides, the sizes, the squares, the
offsets. -/
def VtKeep (σ : Val) (so side bk sq off : E) : Prop :=
  σ (.n 24) = so ∧ σ (.n 25) = side ∧ σ (.n 9) = bk ∧ σ (.n 10) = sq ∧ σ (.n 128) = off

section
variable {C : CallRel} {rd : Reader}

theorem vtKeep_ext {σ σ' : Val} {lo hi : ℕ} (he : Ext lo hi σ σ') (hlo : 128 < lo) {so side bk sq off : E}
    (h : VtKeep σ so side bk sq off) : VtKeep σ' so side bk sq off :=
  ⟨he.get (by omega) h.1, he.get (by omega) h.2.1, he.get (by omega) h.2.2.1,
    he.get (by omega) h.2.2.2.1, he.get (by omega) h.2.2.2.2⟩

/-- **A side's rank `0`** at value `v`: block `b`, size `κ`, offset `1`. -/
theorem vt_c_rank0 (hlow : LowDef 7 rd) {v so0 sd : ℕ} (hv : 128 < v) {σ : Val} {so side bk sq off : E}
    (hk : VtKeep σ so side bk sq off) {b K : ℕ} (hb : b < 102)
    (lso : LoadHolds rd so so0 (gen ^ b)) (lside : LoadHolds rd side b (word sd 0 0))
    (lbk : LoadHolds rd bk b (gen ^ K)) (loff : LoadHolds rd off b 1)
    (lsq : LoadHolds rd sq K (gen ^ 2 ^ K)) :
    Completes C rd v (v + 14) (vtRank0 v so0 sd) σ (fun σ' => VtKeep σ' so side bk sq off ∧
      σ' (.n v) = gen ^ b ∧ σ' (.n (v + 9)) = gen ^ K ∧ σ' (.n (v + 13)) = gen ^ 2 ^ K) := by
  obtain ⟨r1, r2, r3⟩ := rc_complete_low hlow (K := 102) (e := b) (by norm_num) hb
  set L : List (ℕ × E) := [(v, gen ^ b), (v + 1, w101), (v + 2, (rcLow rd b 102).1),
    (v + 3, (rcLow rd b 102).2.1), (v + 4, (rcLow rd b 102).2.2), (v + 5, side * gen ^ b),
    (v + 6, word sd 0 0), (v + 7, word sd 0 0), (v + 8, bk * gen ^ b), (v + 9, gen ^ K),
    (v + 10, word 1 0 0), (v + 11, off * gen ^ b), (v + 12, sq * gen ^ K), (v + 13, gen ^ 2 ^ K)]
    with hL
  have hlo : ∀ p ∈ L, v ≤ p.1 ∧ p.1 < v + 14 := by
    simp only [hL, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      dsimp only <;> omega
  have hk' := vtKeep_ext (upds_ext σ L hlo) hv hk
  obtain ⟨k24, k25, k9, k10, k128⟩ := id hk'
  refine completes_upds L hlo (fun next kret hn => ?_) ⟨hk', ?_, ?_, ?_⟩
  · simp only [vtRank0, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [k24, k25, k9, k10, k128]
    simp only [hL]
    fl_ev
    refine ⟨lso, trivial, ⟨by rw [gen_pow_eq_ofK]; exact r1, by
      show word 3710851743744 0 0 = _; rw [word_g101, gen_pow_eq_ofK]; exact r2, r3⟩, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lside, trivial, e_add_self _, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lbk, trivial, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero, word_one]; exact loff, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lsq, hn⟩
  all_goals simp only [hL]; fl_ev

/-- **A side's rank `≥ 1`** at value `v`: block `b`, size `κ ≤ κ'` (the previous rank's, at
`pk`), on a tie a block past the previous one (at `pg`), the offset `g^S` at `pgo`. -/
theorem vt_c_rankN (hlow : LowDef 7 rd) {v pk pg pgo so0 sd : ℕ} (hv : 128 < v) (hpk : pk < v)
    (hpg : pg < v) (hpgo : pgo < v) {σ : Val} {so side bk sq off : E}
    (hk : VtKeep σ so side bk sq off) {b b' K K' S : ℕ} (hb : b < 102) (hK' : K' < 34)
    (hKK : K ≤ K') (htie : K = K' → b' ≤ b) (spk : σ (.n pk) = gen ^ K') (spg : σ (.n pg) = gen ^ b')
    (spgo : σ (.n pgo) = gen ^ S)
    (lso : LoadHolds rd so so0 (gen ^ b)) (lside : LoadHolds rd side b (word sd 0 0))
    (lbk : LoadHolds rd bk b (gen ^ K)) (loff : LoadHolds rd off b (gen ^ S))
    (lsq : LoadHolds rd sq K (gen ^ 2 ^ K)) :
    Completes C rd v (v + 25) (vtRankN v pk pg pgo so0 sd) σ (fun σ' => VtKeep σ' so side bk sq off ∧
      σ' (.n v) = gen ^ b ∧ σ' (.n (v + 9)) = gen ^ K ∧ σ' (.n (v + 24)) = gen ^ (S + 2 ^ K)) := by
  obtain ⟨r1, r2, r3⟩ := rc_complete_low hlow (K := 102) (e := b) (by norm_num) hb
  obtain ⟨q1, q2, q3⟩ := rc_complete_low hlow (K := 34) (e := K' - K) (by norm_num) (by omega)
  obtain ⟨t1, t2, t3⟩ := rc_complete_low hlow (K := 102) (e := b - b') (by norm_num) (by omega)
  set L : List (ℕ × E) := [(v, gen ^ b), (v + 1, w101), (v + 2, (rcLow rd b 102).1),
    (v + 3, (rcLow rd b 102).2.1), (v + 4, (rcLow rd b 102).2.2), (v + 5, side * gen ^ b),
    (v + 6, word sd 0 0), (v + 7, word sd 0 0), (v + 8, bk * gen ^ b), (v + 9, gen ^ K),
    (v + 10, w33), (v + 11, gen ^ (K' - K)), (v + 12, (rcLow rd (K' - K) 34).1),
    (v + 13, (rcLow rd (K' - K) 34).2.1), (v + 14, (rcLow rd (K' - K) 34).2.2),
    (v + 15, gen ^ K' + gen ^ K), (v + 16, w101), (v + 17, gen ^ (b - b')),
    (v + 18, (rcLow rd (b - b') 102).1), (v + 19, (rcLow rd (b - b') 102).2.1),
    (v + 20, (rcLow rd (b - b') 102).2.2), (v + 21, off * gen ^ b), (v + 22, sq * gen ^ K),
    (v + 23, gen ^ 2 ^ K), (v + 24, gen ^ S * gen ^ 2 ^ K)] with hL
  have hlo : ∀ p ∈ L, v ≤ p.1 ∧ p.1 < v + 25 := by
    simp only [hL, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> omega
  have hk' := vtKeep_ext (upds_ext σ L hlo) hv hk
  obtain ⟨k24, k25, k9, k10, k128⟩ := id hk'
  have hn : ∀ j < v, upds σ L (.n j) = σ (.n j) := fun j hj =>
    upds_ext σ L hlo (.n j) fun k hk1 _ he => by cases he; omega
  refine completes_upds L hlo (fun next kret hn' => ?_) ⟨hk', ?_, ?_, ?_⟩
  · simp only [vtRankN]
    rw [Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
      Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
      Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, holds_ite_noRet _ _ _ rfl rfl]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [k24, k25, k9, k10, k128, hn pk hpk, hn pg hpg, hn pgo hpgo, spk, spg, spgo]
    simp only [hL]
    fl_ev
    have g1 : ∀ e, LoadHolds rd (ofK (Parameters.gpow e)) 0 ((rd (Parameters.gpow e)).getD 0) →
        LoadHolds rd (gen ^ e) 0 ((rd (Parameters.gpow e)).getD 0) := fun e h => by
      rw [gen_pow_eq_ofK]; exact h
    refine ⟨lso, trivial, ⟨g1 _ r1, by
        show word 3710851743744 0 0 = _; rw [word_g101, gen_pow_eq_ofK]; exact r2, r3⟩, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lside, trivial, e_add_self _, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lbk, trivial, by
        rw [← pow_add, Nat.sub_add_cancel hKK], ⟨g1 _ q1, by
        show word 8589934592 0 0 = _; rw [word_g33, gen_pow_eq_ofK]; exact q2, q3⟩, trivial,
      ⟨isInK_add (gen_pow_isInK _) (gen_pow_isInK _), fun hz => ?_, fun _ => trivial⟩, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact loff, trivial, by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lsq, trivial, hn'⟩
    have heq : K' = K := gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp hz)
    have hbb := htie heq.symm
    exact ⟨trivial, by rw [← pow_add, Nat.sub_add_cancel hbb], ⟨g1 _ t1, by
      show word 3710851743744 0 0 = _; rw [word_g101, gen_pow_eq_ofK]; exact t2, t3⟩, trivial⟩
  all_goals simp only [hL]; fl_ev
  rw [pow_add]

/-- A side's sizes: blocks `start ..< start + n`. -/
def vtL (ks : ℕ → ℕ) (start n : ℕ) : List ℕ := (List.range n).map fun i => ks (start + i)

/-- A side's ranks, from value `v0`, its order entries from `so0`. -/
def vtSide (v0 so0 sd n : ℕ) : List Stmt :=
  vtRank0 v0 so0 sd ++ ((List.range (n - 1)).map fun q =>
    vtRankN (rkV v0 q) (rkKa v0 q) (rkGl v0 q) (rkGo v0 q) (so0 + (q + 1)) sd).flatten

/-- **A side's ranks complete** on `stackOrder`'s order of its sizes and their `stackOffsets`
offsets. -/
theorem vt_side_complete (hlow : LowDef 7 rd) {v0 so0 sd start n : ℕ} (hv0 : 128 < v0) (hn : 1 ≤ n)
    (hsn : start + n ≤ 102) {ks : ℕ → ℕ} (hks : ∀ b < 102, ks b < 34)
    (hnb0 : NumBelow (v0 + 14) (Stmt.valsList (vtRank0 v0 so0 sd)))
    (hnb : ∀ q < n - 1, NumBelow (rkV v0 (q + 1)) (Stmt.valsList
      (vtRankN (rkV v0 q) (rkKa v0 q) (rkGl v0 q) (rkGo v0 q) (so0 + (q + 1)) sd)))
    {σ : Val} {so side bk sq off : E} (hk : VtKeep σ so side bk sq off)
    (lso : ∀ r < n, LoadHolds rd so (so0 + r) (gen ^ (start + cpPi (vtL ks start n) r)))
    (lside : ∀ i < n, LoadHolds rd side (start + i) (word sd 0 0))
    (lbk : ∀ b < 102, LoadHolds rd bk b (gen ^ ks b))
    (lsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (loff : ∀ i < n, LoadHolds rd off (start + i) (gen ^ (stackOffsets (vtL ks start n)).1.getD i 0)) :
    Completes C rd v0 (rkV v0 (n - 1)) (vtSide v0 so0 sd n) σ
      (fun σ' => VtKeep σ' so side bk sq off) := by
  set L := vtL ks start n with hLdef
  have hlen : L.length = n := by simp [hLdef, vtL]
  have hol : (stackOrder L).length = n := by rw [stackOrder_length, hlen]
  have hperm : (stackOrder L).Perm (List.range n) := by
    rw [← hlen]; exact List.mergeSort_perm _ _
  have hπ : ∀ r < n, cpPi L r < n := fun r hr => by
    have := hperm.subset (List.getElem_mem (show r < (stackOrder L).length by omega))
    rw [cpPi, List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_range.mp this
  have hK : ∀ r < n, cpK L r = ks (start + cpPi L r) := fun r hr => by
    rw [cpK, hLdef, vtL, List.getD_eq_getElem _ _ (by simp; exact hπ r hr), List.getElem_map,
      List.getElem_range]
  have hk34 : ∀ r < n, cpK L r < 34 := fun r hr => by rw [hK r hr]; exact hks _ (by have := hπ r hr; omega)
  have hoff : ∀ r < n, LoadHolds rd off (start + cpPi L r) (gen ^ cpS L r) := fun r hr => by
    have := loff (cpPi L r) (hπ r hr)
    rwa [cpPi, stackOrder, stackOffsets_fst L r (by omega)] at this
  have hbk : ∀ r < n, LoadHolds rd bk (start + cpPi L r) (gen ^ cpK L r) := fun r hr => by
    rw [hK r hr]; exact lbk _ (by have := hπ r hr; omega)
  have hS0 : cpS L 0 = 0 := by simp [cpS, prefixSize]
  unfold vtSide
  refine Completes.append (m := v0 + 14) (by omega) (by simp [rkV]) hnb0
    (vt_c_rank0 (C := C) hlow hv0 hk (b := start + cpPi L 0) (K := cpK L 0) (by have := hπ 0 hn; omega)
      (by simpa using lso 0 hn) (lside _ (hπ 0 hn)) (hbk 0 hn) (by have := hoff 0 hn; rwa [hS0, pow_zero] at this)
      (lsq _ (hk34 0 hn))) fun σ1 e1 ⟨k1, g1, kk1, go1⟩ => ?_
  have hst : ∀ q, rkV v0 q = v0 + 14 + 25 * q := fun q => rfl
  refine (Completes.flatten (st := rkV v0) (Inv := fun q σ => VtKeep σ so side bk sq off ∧
      σ (.n (rkKa v0 q)) = gen ^ cpK L q ∧ σ (.n (rkGl v0 q)) = gen ^ (start + cpPi L q) ∧
      σ (.n (rkGo v0 q)) = gen ^ cpS L (q + 1)) (n - 1) (fun q _ => by simp only [hst]; omega)
    hnb (fun q hq σ ⟨kq, kaq, glq, goq⟩ => ?_) σ1 ⟨k1, kk1, g1, ?_⟩).mono le_rfl le_rfl
    fun σ' h => h.1
  · obtain ⟨ha1, ha2⟩ := stackOrder_adj L (r := q) (by omega)
    have hgl : rkGl v0 q < rkV v0 q := by unfold rkGl rkV; split_ifs <;> omega
    have hka : rkKa v0 q < rkV v0 q := by unfold rkKa rkGl rkV; split_ifs <;> omega
    have hgo : rkGo v0 q < rkV v0 q := by unfold rkGo rkV; omega
    refine (vt_c_rankN (C := C) hlow (by unfold rkV; omega) hka hgl hgo kq
      (b := start + cpPi L (q + 1)) (b' := start + cpPi L q) (K := cpK L (q + 1)) (K' := cpK L q)
      (S := cpS L (q + 1)) (by have := hπ (q + 1) (by omega); omega) (hk34 q (by omega)) ha1
      (fun h => by have := ha2 h.symm; omega) kaq glq goq (lso _ (by omega))
      (lside _ (hπ _ (by omega))) (hbk _ (by omega)) (hoff _ (by omega))
      (lsq _ (hk34 _ (by omega)))).mono le_rfl (by simp [rkV]; omega) fun σ' ⟨kp, gp, kkp, gop⟩ => ?_
    have e1 : rkKa v0 (q + 1) = rkV v0 q + 9 := by simp [rkKa, rkGl]
    have e2 : rkGl v0 (q + 1) = rkV v0 q := by simp [rkGl]
    have e3 : rkGo v0 (q + 1) = rkV v0 q + 24 := by simp only [rkGo, rkV]; ring
    refine ⟨kp, by rw [e1]; exact kkp, by rw [e2]; exact gp, by
      rw [e3, gop, cpS_succ L (r := q + 1) (by omega)]⟩
  · rw [show rkGo v0 0 = v0 + 13 by rfl, go1, cpS_succ L (by omega), hS0, Nat.zero_add]

end

set_option maxRecDepth 100000 in
/-- The segment is the push side's ranks, then the count side's. -/
theorem vt_sort_seg : stmtsEqb (vtSide 129 0 0 37 ++ vtSide 1043 74 2 28) ((vtPre.drop 213).take 1225) =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vt_sort_nb : numBelowB 1043 (Stmt.valsList (vtSide 129 0 0 37)) = true ∧
    numBelowB 143 (Stmt.valsList (vtRank0 129 0 0)) = true ∧
    numBelowB 1057 (Stmt.valsList (vtRank0 1043 74 2)) = true ∧
    (∀ q < 36, numBelowB (rkV 129 (q + 1)) (Stmt.valsList
      (vtRankN (rkV 129 q) (rkKa 129 q) (rkGl 129 q) (rkGo 129 q) (0 + (q + 1)) 0)) = true) ∧
    ∀ q < 27, numBelowB (rkV 1043 (q + 1)) (Stmt.valsList
      (vtRankN (rkV 1043 q) (rkKa 1043 q) (rkGl 1043 q) (rkGo 1043 q) (74 + (q + 1)) 2)) = true := by
  decide +kernel

/-- **The certified block order completes** (`VtSortComplete`). -/
theorem vt_sort_complete : VtSortComplete := by
  intro κ hκ rd hlow ks hks σ so side bk sq off h24 h25 h9 h10 h128 lsoP lsoC lside lbk lsq loffP
    loffC
  rw [← stmtsEqb_sound vt_sort_seg]
  obtain ⟨n0, n1, n2, n3, n4⟩ := vt_sort_nb
  have hl7 := hlow.mono hκ
  have hLP : vtL ks 0 37 = (List.range 37).map ks := by simp [vtL]
  refine Completes.append (m := 1043) (by omega) (by omega) (numBelow_of_B n0)
    (vt_side_complete (v0 := 129) (so0 := 0) (sd := 0) (start := 0) (n := 37) hl7 (by omega)
      (by omega) (by omega) hks (numBelow_of_B n1) (fun q hq => numBelow_of_B (n3 q hq))
      ⟨h24, h25, h9, h10, h128⟩ (fun r hr => ?_) (fun i hi => ?_) lbk lsq (fun i hi => ?_))
    fun σ1 _ k1 => (vt_side_complete (v0 := 1043) (so0 := 74) (sd := 2) (start := 74) (n := 28) hl7
      (by omega) (by omega) (by omega) hks (numBelow_of_B n2) (fun q hq => numBelow_of_B (n4 q hq))
      k1 (fun r hr => lsoC r hr) (fun i hi => ?_) lbk lsq (fun i hi => loffC i hi)).mono le_rfl
      le_rfl fun _ _ => trivial
  · rw [hLP, Nat.zero_add, Nat.zero_add]; exact lsoP r hr
  · have := lside (0 + i) (by omega)
    rwa [show vtBlockSide (0 + i) = 0 by unfold vtBlockSide; split_ifs <;> omega] at this
  · rw [hLP, Nat.zero_add]; exact loffP i hi
  · have := lside (74 + i) (by omega)
    rwa [show vtBlockSide (74 + i) = 2 by unfold vtBlockSide; split_ifs <;> omega] at this

end
end LeanVM.Guest.B1.VerifySub
