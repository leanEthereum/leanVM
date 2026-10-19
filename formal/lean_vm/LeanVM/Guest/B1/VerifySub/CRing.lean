/-
  LeanVM.Guest.B1.VerifySub.CRing

  `verify_sub`'s ring-switching block, complete: the map's challenges, `c_table`, the target
  through `__loop84`, and Flock's point copied into `z_vals`.
-/

module

public import LeanVM.Guest.B1.VerifySub.CLoops

/-!
# The ring switch, complete (G:2170-2210)

* `ctTab_stable`: an entry of `c_table` set at a stage is never changed after it;
* `c_ctSlot`, `c_ctStage`: one slot, one stage of `c_table`;
* `c_ring`: the block.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs} {out : E}

/-! ## `c_table` -/

theorem ctD_dvd : ∀ st < 6, ∀ s < 6, st < s → 2 * ctD s ∣ ctD st := by decide

theorem ctD_pos : ∀ s < 6, 0 < ctD s := by decide

/-- **`c_table`'s entries at multiples of a stage's shift are final after it.** -/
theorem ctTab_stable (mcs : List E) {st k : ℕ} (hst : st < 6) (hk : k % ctD st = 0) :
    ∀ s, st + 1 ≤ s → s ≤ 6 → ctTab mcs s k = ctTab mcs (st + 1) k := by
  intro s h1 h2
  induction s with
  | zero => omega
  | succ s ih =>
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [h]
    · have hd := ctD_dvd st hst s (by omega) (by omega)
      have hp := ctD_pos s (by omega)
      have hm : k % (2 * ctD s) = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans hd (Nat.dvd_of_mod_eq_zero hk))
      simp only [ctTab, hm, show (0 : ℕ) ≠ ctD s by omega, ↓reduceIte]
      exact ih (by omega) (by omega)

theorem ctTab_keep (mcs : List E) {st sl : ℕ} (hst : st < 6) :
    ctTab mcs (st + 1) (sl * (2 * ctD st)) = ctTab mcs st (sl * (2 * ctD st)) := by
  have hp := ctD_pos st hst
  simp only [ctTab, Nat.mul_mod_left, show (0 : ℕ) ≠ ctD st by omega, ↓reduceIte]

theorem ctTab_set (mcs : List E) {st sl : ℕ} (hst : st < 6) :
    ctTab mcs (st + 1) (sl * (2 * ctD st) + ctD st) =
      mcs.getD st 0 * ctTab mcs st (sl * (2 * ctD st)) ^ 2 ^ ctD st := by
  have hp := ctD_pos st hst
  have hm : (sl * (2 * ctD st) + ctD st) % (2 * ctD st) = ctD st := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
  simp only [ctTab, hm, ↓reduceIte, Nat.add_sub_cancel]

/-- `c_table`'s final words, stage by stage. -/
theorem ctab_at (mcs : List E) (hl : mcs.length = 6) {st sl : ℕ} (hst : st < 6)
    (hsl : sl < 2 ^ st) :
    (ringCoefficients mcs).getD (sl * (2 * ctD st)) 0 = ctTab mcs st (sl * (2 * ctD st)) ∧
      (ringCoefficients mcs).getD (sl * (2 * ctD st) + ctD st) 0 =
        mcs.getD st 0 * ctTab mcs st (sl * (2 * ctD st)) ^ 2 ^ ctD st := by
  obtain ⟨hd0, -, -, hd3⟩ := ctD_facts st hst
  have hlt : sl * (2 * ctD st) + ctD st < 64 := by
    have : (sl + 1) * (2 * ctD st) ≤ 2 ^ st * (2 * ctD st) := Nat.mul_le_mul_right _ (by omega)
    rw [hd3] at this; nlinarith
  constructor
  · rw [← ctTab_six mcs hl _ (by omega), ctTab_stable mcs hst (by
      rw [Nat.mul_mod, show 2 * ctD st % ctD st = 0 by simp]; simp) 6 (by omega) le_rfl,
      ctTab_keep mcs hst]
  · rw [← ctTab_six mcs hl _ hlt, ctTab_stable mcs hst (by
      rw [Nat.add_mod, Nat.mul_mod, show 2 * ctD st % ctD st = 0 by simp]; simp) 6 (by omega) le_rfl,
      ctTab_set mcs hst]

/-- The honest values of slot `sl` of stage `st`. -/
def ctVals (mcs : List E) (st sl : ℕ) (i : ℕ) : E :=
  if i ≤ ctD st then ctTab mcs st (sl * (2 * ctD st)) ^ 2 ^ i
  else mcs.getD st 0 * ctTab mcs st (sl * (2 * ctD st)) ^ 2 ^ ctD st

theorem holds_sqChain_complete {C : CallRel} {σ : Val} {k : List E → Prop} (u d : ℕ) (w : E)
    (hs : ∀ i ≤ d, σ (.n (u + i)) = w ^ 2 ^ i) :
    Stmt.HoldsList C rd σ (sqChain u d) True k := by
  rw [sqChain, holdsList_range_flatten d _ (fun _ => rfl)]
  refine ⟨fun i hi => ⟨?_, trivial⟩, trivial⟩
  show σ (.n (u + 1 + i)) = σ (.n (u + i)) * σ (.n (u + i))
  rw [show u + 1 + i = u + (i + 1) by omega, hs (i + 1) (by omega), hs i (by omega), ← pow_two,
    ← pow_mul, pow_succ]

/-- **Slot `sl` of stage `st` of `c_table`** (G:2183-2188). -/
theorem c_ctSlot (hl : D.mcs.length = 6) {st sl : ℕ} (hst : st < 6) (hsl : sl < 2 ^ st)
    (hct : ReadsAt rd P.ctab (ringCoefficients D.mcs)) (σ : Val) (h733 : σ (.n 733) = P.ctab)
    (hc : σ (.n (ctV st)) = D.mcs.getD st 0) (hlt : 733 < ctV st) :
    Completes C rd (ctV st + 1 + sl * (ctD st + 2))
      (ctV st + 1 + sl * (ctD st + 2) + (ctD st + 2)) (ctSlot st sl) σ
      (fun σ' => σ' (.n 733) = P.ctab ∧ σ' (.n (ctV st)) = D.mcs.getD st 0) := by
  set u := ctV st + 1 + sl * (ctD st + 2)
  obtain ⟨h0, h1⟩ := ctab_at D.mcs hl hst hsl
  have hrc : ∀ k < 64, LoadHolds rd P.ctab k ((ringCoefficients D.mcs).getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [ringCoefficients, kBits] using hk)]
    exact hct k (by simpa [ringCoefficients, kBits] using hk)
  obtain ⟨hd0, -, -, hd3⟩ := ctD_facts st hst
  have hlt64 : sl * (2 * ctD st) + ctD st < 64 := by
    have : (sl + 1) * (2 * ctD st) ≤ 2 ^ st * (2 * ctD st) := Nat.mul_le_mul_right _ (by omega)
    rw [hd3] at this; nlinarith
  refine completes_setv (ctVals D.mcs st sl) (fun next kret hn => ?_) ?_
  · rw [ctSlot, holdsList_append, holdsList_append]
    have hs : ∀ i ≤ ctD st, setv σ u (ctD st + 2) (ctVals D.mcs st sl) (.n (u + i)) =
        ctTab D.mcs st (sl * (2 * ctD st)) ^ 2 ^ i := fun i hi => by
      rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]; simp [ctVals, hi]
    have hlast : setv σ u (ctD st + 2) (ctVals D.mcs st sl) (.n (u + ctD st + 1)) =
        D.mcs.getD st 0 * ctTab D.mcs st (sl * (2 * ctD st)) ^ 2 ^ ctD st := by
      rw [set_n_in (by omega) (by omega), show u + ctD st + 1 - u = ctD st + 1 by omega]
      simp [ctVals]
    have e733 : setv σ u (ctD st + 2) (ctVals D.mcs st sl) (.n 733) = P.ctab := by
      rw [set_n_lt (by omega)]; exact h733
    have ec : setv σ u (ctD st + 2) (ctVals D.mcs st sl) (.n (ctV st)) = D.mcs.getD st 0 := by
      rw [set_n_lt (by omega)]; exact hc
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    refine ⟨?_, ?_⟩
    · have hs0 := hs 0 (by omega)
      simp only [Nat.add_zero, pow_zero, pow_one] at hs0
      rw [e733]
      change LoadHolds rd P.ctab (sl * (2 * ctD st)) (setv σ u (ctD st + 2) (ctVals D.mcs st sl) (.n u))
      rw [hs0, ← h0]
      exact hrc _ (by omega)
    · rw [holdsList_noRet _ (sqChain_noRet _ _)]
      refine ⟨holds_sqChain_complete u (ctD st) _ hs, ?_, ?_, hn⟩
      · rw [hlast, ec, hs (ctD st) le_rfl]
      · rw [e733, hlast, ← h1]; exact hrc _ hlt64
  · refine ⟨?_, ?_⟩
    · rw [set_n_lt (by omega)]; exact h733
    · rw [set_n_lt (by omega)]; exact hc

theorem ctV_succ (st : ℕ) : ctV (st + 1) = ctV st + 1 + 2 ^ st * (ctD st + 2) := rfl

theorem ctV_ge : ∀ st ≤ 6, 820 ≤ ctV st := by decide

theorem ctV_six : ctV 6 = 1144 := by decide

theorem numBelow_ctSlot : ∀ st < 6, ∀ sl < 2 ^ st,
    NumBelow (ctV st + 1 + (sl + 1) * (ctD st + 2)) (Stmt.valsList (ctSlot st sl)) :=
  fun st hst sl hsl => numBelow_of_B (by revert st hst sl hsl; decide +kernel)

theorem numBelow_ctStage : ∀ st < 6, NumBelow (ctV (st + 1)) (Stmt.valsList (ctStage st)) :=
  fun st hst => numBelow_of_B (by revert st hst; decide +kernel)

/-- **Stage `st` of `c_table`** (G:2181-2189). -/
theorem c_ctStage (hl : D.mcs.length = 6) {st : ℕ} (hst : st < 6)
    (hct : ReadsAt rd P.ctab (ringCoefficients D.mcs)) (hm : LoadHolds rd P.mcs st (D.mcs.getD st 0))
    (σ : Val) (h732 : σ (.n 732) = P.mcs) (h733 : σ (.n 733) = P.ctab) :
    Completes C rd (ctV st) (ctV (st + 1)) (ctStage st) σ
      (fun σ' => σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) := by
  have hge := ctV_ge st (by omega)
  rw [ctStage, ← List.singleton_append, ctV_succ]
  refine Completes.append (m := ctV st + 1) (P := fun σ' => σ' (.n 732) = P.mcs ∧
      σ' (.n 733) = P.ctab ∧ σ' (.n (ctV st)) = D.mcs.getD st 0) (by omega) (by omega)
    (numBelow_of_B (by simp [numBelowB, Stmt.vals, Atom.vals]; omega)) ?_ fun σ1 _ ⟨i732, i733, ic⟩ => ?_
  · refine completes_upds [(ctV st, D.mcs.getD st 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil,
        show (732 : ℕ) ≠ ctV st by omega, ↓reduceIte, h732]
      exact ⟨hm, hn⟩
    · simp only [upds_n, upds_nil, show (732 : ℕ) ≠ ctV st by omega,
        show (733 : ℕ) ≠ ctV st by omega, ↓reduceIte, h732, h733]
      exact ⟨trivial, trivial, trivial⟩
  · have key := Completes.flatten (C := C) (rd := rd) (blk := ctSlot st)
      (st := fun sl ↦ ctV st + 1 + sl * (ctD st + 2)) (Inv := fun _ σ' ↦ σ' (.n 732) = P.mcs ∧
        σ' (.n 733) = P.ctab ∧ σ' (.n (ctV st)) = D.mcs.getD st 0) (2 ^ st)
      (fun sl _ => by show _ + sl * _ ≤ _ + (sl + 1) * _; rw [Nat.succ_mul]; omega) (numBelow_ctSlot st hst)
      (fun sl hsl σ' ⟨j732, j733, jc⟩ => by
        have c := (c_ctSlot (C := C) hl hst hsl hct σ' j733 jc (by omega)).keep (l := [(732, P.mcs)])
          (by intro p hp; simp at hp; subst hp; exact j732) (by simp; omega)
        rw [show ctV st + 1 + (sl + 1) * (ctD st + 2) = ctV st + 1 + sl * (ctD st + 2) + (ctD st + 2)
          by ring]
        exact c.post fun σ'' _ ⟨⟨k733, kc⟩, kf⟩ => ⟨kf.get (by simp), k733, kc⟩) σ1 ⟨i732, i733, ic⟩
    simp only [Nat.zero_mul, Nat.add_zero] at key
    exact key.post fun σ' _ ⟨k1, k2, _⟩ => ⟨k1, k2⟩

/-! ## `rs_chain` -/

theorem getD_flatMap_pair (a b : ℕ → E) :
    ∀ n j, j < n → ((List.range n).flatMap fun i ↦ [a i, b i]).getD (2 * j) 0 = a j ∧
      ((List.range n).flatMap fun i ↦ [a i, b i]).getD (2 * j + 1) 0 = b j ∧
      ((List.range n).flatMap fun i ↦ [a i, b i]).length = 2 * n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    have hlen : ((List.range n).flatMap fun i ↦ [a i, b i]).length = 2 * n := by
      induction n with
      | zero => rfl
      | succ n ih => rw [List.range_succ, List.flatMap_append]; simp; ring
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, hlen,
      List.length_cons, List.length_nil]
    refine ⟨?_, ?_, by ring⟩
    · rcases Nat.lt_or_ge j n with hj | hj
      · rw [List.getD_append _ _ _ _ (by omega)]; exact (getD_flatMap_pair a b n j hj).1
      · rw [show j = n by omega, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]; rfl
    · rcases Nat.lt_or_ge j n with hj | hj
      · rw [List.getD_append _ _ _ _ (by omega)]; exact (getD_flatMap_pair a b n j hj).2.1
      · rw [show j = n by omega, List.getD_append_right _ _ _ _ (by omega), hlen,
          show 2 * n + 1 - 2 * n = 1 by omega]; rfl

/-- The running sum of `rs_chain`'s row `j`. -/
def rsSum (D : VsData) (j : ℕ) : E := ((List.range j).map fun i ↦ phiMap (D.s.getD i 0) D.mcs * gen ^ i).sum

theorem rsChain_at {j : ℕ} (hj : j ≤ 64) :
    D.rsChain.getD (2 * j) 0 = gen ^ j ∧ D.rsChain.getD (2 * j + 1) 0 = rsSum D j ∧
      D.rsChain.length = 130 :=
  getD_flatMap_pair _ _ 65 j (by omega)

theorem readsAt_getD {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **`__loop84`'s bodies over the honest `rs_chain`.** -/
theorem loop84_bodies (hm : VsMem0 rd D P out) (hs : D.s.length = 64) (hl : D.mcs.length = 6) :
    ∀ j < 64, Loop84Body rd P.zpart P.mcs P.rs (gen ^ j) := by
  intro j hj
  obtain ⟨a0, b0, hlen⟩ := rsChain_at (D := D) (j := j) (by omega)
  obtain ⟨a1, b1, -⟩ := rsChain_at (D := D) (j := j + 1) (by omega)
  have hr : ∀ k < 4, LoadHolds rd (P.rs * (gen ^ j * gen ^ j)) k (D.rsChain.getD (2 * j + k) 0) :=
    fun k hk => by
      rw [gen_pow_two_mul, loadHolds_mul_gen_pow]
      exact readsAt_getD hm.rs (by rw [hlen]; omega)
  refine ⟨D.s.getD j 0, gen ^ j, rsSum D j, D.mcs, hl, hm.mcs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact readsAt_getD hm.zpart (by omega)
  · have := hr 0 (by omega); rwa [Nat.add_zero, a0] at this
  · have := hr 1 (by omega); rwa [b0] at this
  · have := hr 2 (by omega); rwa [show 2 * j + 2 = 2 * (j + 1) by ring, a1, pow_succ] at this
  · have := hr 3 (by omega)
    rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring, b1] at this
    convert this using 1
    simp only [rsSum, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    ring

/-! ## The block -/

theorem word325 : word 325 0 0 = gen ^ 128 := by
  rw [word_eOfNat, show (325 : ℕ) = gSquaresBits.getD 7 0 from rfl, eOfNat_gSquaresBits 7 (by decide)]
  norm_num

theorem rsSum_target (hs : D.s.length = 64) : rsSum D 64 = ringTarget D.s D.mcs := by
  rw [ringTarget, polyEval_eq_sum, List.length_map, hs, rsSum]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' : i < 64 := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa [hs] using hi'), List.getD_eq_getElem _ _ (by simpa [hs] using hi'),
    List.getElem_map]

/-- The values the ring block reads. -/
def ringIn (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(718, gen ^ D.tau), (721, P.zchis), (722, P.lrs), (723, P.zpart), (730, (digestScalars D.cvF).1),
    (731, (digestScalars D.cvF).2), (732, P.mcs), (733, P.ctab), (734, P.zvals)]

/-- The values the ring block leaves. -/
def ringOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(810, (digestScalars D.cvM).1), (811, (digestScalars D.cvM).2), (1144, P.rs),
    (1149, P.rs * word 325 0 0), (1150, ringTarget D.s D.mcs), (1160, word 1 0 0 + gen ^ D.tau)]

theorem bRing_eq : bRing = bSqueezes 6 730 735 (.n 732) ++
    [.atom (.const (.n 819) (word 1 0 0)), .atom (.load (.n 819) (.n 733) 0)] ++
    ((List.range 6).map ctStage).flatten ++
    [.atom (.hint (.alloc (.n 1144) 130)), .atom (.const (.n 1145) (word 1 0 0)),
      .atom (.load (.n 1145) (.n 1144) 0), .atom (.const (.n 1146) (word 0 0 0)),
      .atom (.load (.n 1146) (.n 1144) 1), .atom (.const (.n 1147) (word 1 0 0)),
      .call "__loop84" [.n 1147, .n 723, .n 732, .n 1144] [],
      .atom (.const (.n 1148) (word 325 0 0)), .atom (.mul (.n 1149) (.n 1144) (.n 1148)),
      .atom (.load (.n 1150) (.n 1149) 1)] ++
    ((List.range 8).map fun t ↦ [.atom (.load (.n (1151 + t)) (.n 722) (7 - t)),
      .atom (.load (.n (1151 + t)) (.n 734) t)]).flatten ++
    [.atom (.const (.n 1159) (word 1 0 0)), .atom (.add (.n 1160) (.n 1159) (.n 718)),
      .atom (.const (.n 1161) (word 1 0 0)), .atom (.const (.n 1162) (word 256 0 0)),
      .atom (.mul (.n 1163) (.n 734) (.n 1162)), .atom (.const (.n 1164) (word 256 0 0)),
      .atom (.mul (.n 1165) (.n 721) (.n 1164)),
      .callIf (.n 1160) "__loop85" [.n 1161, .n 718, .n 1163, .n 1165]] := rfl

theorem mcs_eq : D.mcs = (List.range 6).map fun k ↦ challengeOf (sqCv^[k + 1] D.cvF) := by
  simp [VsData.mcs, sqAll_eq]

theorem mcs_length : D.mcs.length = 6 := by simp [mcs_eq]

theorem numBelow_sq732 : ∀ k < 6, NumBelow (735 + 14 * (k + 1)) (Stmt.valsList (sqBlk 730 735 (.n 732) k)) :=
  fun k hk => numBelow_of_B (by revert k hk; decide +kernel)

/-- **The ring switch** (G:2170-2210): the map's challenges, `c_table`, the target, `z_vals`. -/
theorem c_ring {bytecode : List K} {lp sq : E} (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk C bytecode D P lp sq) (σ : Val)
    (hσ : Fixes σ (ringIn D P)) :
    Completes C rd 735 1166 bRing σ (fun σ' => Fixes σ' (ringOut D P)) := by
  have e : ∀ k e, (k, e) ∈ ringIn D P → σ (.n k) = e := fun k e h => hσ.get h
  have hl := mcs_length (D := D)
  have hmc : ∀ k < 6, LoadHolds rd P.mcs k (challengeOf (sqCv^[k + 1] D.cvF)) := fun k hk => by
    have := hm.mcs k (by omega)
    simp only [mcs_eq, List.getElem_map, List.getElem_range] at this
    exact this
  have hmc' : ∀ k < 6, LoadHolds rd P.mcs k (D.mcs.getD k 0) := fun k hk =>
    readsAt_getD hm.mcs (by omega)
  have hτ := tau_lt hok
  rw [bRing_eq]
  refine Completes.append (m := 1159) (P := fun σ' => σ' (.n 1150) = ringTarget D.s D.mcs ∧
      Fixes σ' ([(810, (digestScalars D.cvM).1), (811, (digestScalars D.cvM).2), (1144, P.rs),
        (1149, P.rs * word 325 0 0)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ5 _ ⟨j1150, jf⟩ => ?tailF
  refine Completes.append (m := 1151) (P := fun σ' => σ' (.n 1150) = ringTarget D.s D.mcs ∧
      Fixes σ' ([(810, (digestScalars D.cvM).1), (811, (digestScalars D.cvM).2), (1144, P.rs),
        (1149, P.rs * word 325 0 0)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ4 _ ⟨j1150, jf⟩ => ?copies
  refine Completes.append (m := 1144) (P := fun σ' => (σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) ∧
      Fixes σ' ([(810, (digestScalars D.cvM).1), (811, (digestScalars D.cvM).2)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ3 _ ⟨⟨j732, j733⟩, jf⟩ => ?chain
  refine Completes.append (m := 820) (P := fun σ' => (σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) ∧
      Fixes σ' ([(810, (digestScalars D.cvM).1), (811, (digestScalars D.cvM).2)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ ⟨⟨j732, j733⟩, jf⟩ => ?stages
  refine Completes.append (m := 819) (P := fun σ' => (σ' (.n 732) = P.mcs ∧
      (σ' (.n 810), σ' (.n 811)) = digestScalars D.cvM) ∧ Fixes σ' (ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ ⟨⟨j732, j810⟩, jf⟩ => ?ct0
  · -- the six challenges
    refine ((c_squeezes (m := 6) (s0 := 730) (b0 := 735) (out := .n 732) (po := P.mcs) (cv := D.cvF)
      (by omega) (by omega) ⟨732, by omega, rfl⟩ hmc numBelow_sq732 σ (e 732 P.mcs (by simp [ringIn]))
      (by rw [e 730 (digestScalars D.cvF).1 (by simp [ringIn]),
        e 731 (digestScalars D.cvF).2 (by simp [ringIn])])).keep hσ
      (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp)).post fun σ' _ ⟨⟨k1, k2⟩, kf⟩ => ⟨⟨k1, ?_⟩, kf⟩
    rw [k2]; simp [VsData.cvM, sqAll_eq]
  case ct0 =>
    refine completes_upds [(819, word 1 0 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [jf.get (k := 733) (e := P.ctab) (by simp [ringIn]), word_one]
      have := (ctab_at D.mcs hl (st := 0) (sl := 0) (by omega) (by omega)).1
      simp only [Nat.zero_mul, ctTab, ↓reduceIte] at this
      exact ⟨trivial, by rw [← this]; exact readsAt_getD hm.ctab (by simp [ringCoefficients, kBits]),
        hn⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · vs_ev; exact j732
      · vs_ev; exact jf.get (k := 733) (e := P.ctab) (by simp [ringIn])
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl <;> vs_ev
          · exact congrArg Prod.fst j810
          · exact congrArg Prod.snd j810
        · rw [upds_of_not_mem _ _ (by
            intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq; subst hq
            simp only [ringIn, List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
          exact jf p hp
  case stages =>
    have key := Completes.flatten (C := C) (rd := rd) (blk := ctStage) (st := ctV)
      (Inv := fun _ σ' ↦ σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) 6
      (fun st hst => by rw [ctV_succ]; omega) numBelow_ctStage
      (fun st hst σ' ⟨k1, k2⟩ => c_ctStage hl hst hm.ctab (hmc' st hst) σ' k1 k2) σ2 ⟨j732, j733⟩
    rw [ctV_six] at key
    exact key.keep jf (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ctV])
  case chain =>
    obtain ⟨a0, b0, hlen⟩ := rsChain_at (D := D) (j := 0) (by omega)
    obtain ⟨-, b64, -⟩ := rsChain_at (D := D) (j := 64) (by omega)
    have j723 : σ3 (.n 723) = P.zpart := jf.get (by simp [ringIn])
    refine ((completes_upds [(1144, P.rs), (1145, word 1 0 0), (1146, word 0 0 0), (1147, word 1 0 0),
      (1148, word 325 0 0), (1149, P.rs * word 325 0 0), (1150, rsSum D 64)] (by simp)
      (fun next kret hn => ?_) (Post := fun σ' => σ' (.n 1150) = rsSum D 64 ∧ σ' (.n 1144) = P.rs ∧
        σ' (.n 1149) = P.rs * word 325 0 0)
      (by vs_ev; exact ⟨trivial, trivial, trivial⟩)).keep jf
      (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp)).post fun σ' _ ⟨⟨k1, k3, k4⟩, k2⟩ =>
          ⟨by rw [k1, rsSum_target hok.s_length], fun p hp => by
            rcases List.mem_append.mp hp with hp | hp
            · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl
              · exact k2.get (by simp)
              · exact k2.get (by simp)
              · exact k3
              · exact k4
            · exact k2 p (List.mem_append_right _ hp)⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    rw [j723, j732]
    refine ⟨trivial, trivial, ?_, trivial, ?_, trivial, ?_, trivial, trivial, ?_, hn⟩
    · have h0 : D.rsChain.getD 0 0 = 1 := by simpa using a0
      rw [word_one, ← h0]; exact readsAt_getD hm.rs (by rw [hlen]; omega)
    · rw [word_zero, show (0 : E) = D.rsChain.getD (2 * 0 + 1) 0 by rw [b0]; simp [rsSum]]
      exact readsAt_getD hm.rs (by rw [hlen]; omega)
    · exact hC.loop84
    · rw [word325, loadHolds_mul_gen_pow, ← b64]
      exact readsAt_getD hm.rs (by rw [hlen]; omega)
  case copies =>
    have key := Completes.flatten (C := C) (rd := rd)
      (blk := fun t ↦ [.atom (.load (.n (1151 + t)) (.n 722) (7 - t)),
        .atom (.load (.n (1151 + t)) (.n 734) t)]) (st := fun t ↦ 1151 + t)
      (Inv := fun _ σ' ↦ σ' (.n 722) = P.lrs ∧ σ' (.n 734) = P.zvals) 8 (fun _ _ => by omega)
      (fun t ht => numBelow_of_B (by revert t ht; decide +kernel)) (fun t ht σ' ⟨k1, k2⟩ => ?_) σ4
      ⟨jf.get (by simp [ringIn]), jf.get (by simp [ringIn])⟩
    · exact (key.keep (l := (1150, ringTarget D.s D.mcs) :: ([(810, (digestScalars D.cvM).1),
        (811, (digestScalars D.cvM).2), (1144, P.rs), (1149, P.rs * word 325 0 0)] ++ ringIn D P)) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact j1150
          · exact jf p hp)
        (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)).post fun σ' _ ⟨_, kf⟩ =>
        ⟨kf.get (by simp), fun p hp => kf p (List.mem_cons_of_mem _ hp)⟩
    · have hrv : D.fpoint.getD t 0 = D.rcs.getD (7 - t) 0 := by
        have hrl := hok.rcs_length
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hrl]; omega),
          List.getElem_append_left (by simp [hrl]; omega), List.getElem_reverse,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [hrl]
      refine completes_upds [(1151 + t, D.rcs.getD (7 - t) 0)] (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil,
          show (722 : ℕ) ≠ 1151 + t by omega, show (734 : ℕ) ≠ 1151 + t by omega, ↓reduceIte, k1, k2]
        refine ⟨readsAt_getD hm.lrs (by rw [hok.rcs_length]; omega), ?_, hn⟩
        rw [← hrv]; exact readsAt_getD hm.zvals (by simp [VsData.fpoint, hok.rcs_length]; omega)
      · simp only [upds_n, upds_nil, show (722 : ℕ) ≠ 1151 + t by omega,
          show (734 : ℕ) ≠ 1151 + t by omega, ↓reduceIte, k1, k2, and_self]
  case tailF =>
    have j718 : σ5 (.n 718) = gen ^ D.tau := jf.get (by simp [ringIn])
    have j721 : σ5 (.n 721) = P.zchis := jf.get (by simp [ringIn])
    have j734 : σ5 (.n 734) = P.zvals := jf.get (by simp [ringIn])
    have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
    refine completes_upds [(1159, word 1 0 0), (1160, word 1 0 0 + gen ^ D.tau), (1161, word 1 0 0),
      (1162, word 256 0 0), (1163, P.zvals * word 256 0 0), (1164, word 256 0 0),
      (1165, P.zchis * word 256 0 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
      vs_ev
      rw [j718, j721, j734]
      refine ⟨by vs_triv, by vs_triv, by vs_triv, by vs_triv, by vs_triv, by vs_triv, by vs_triv, ?_, ?_,
        hn⟩
      · rw [word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK 0) (gen_pow_isInK _)
      · intro hne
        refine hC.loop85 fun h => hne ?_
        rw [h, word_one, pow_zero, e_add_eq_zero_iff]
    · intro p hp
      simp only [ringOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> vs_ev
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact j1150

end
end LeanVM.Guest.B1.VerifySub
