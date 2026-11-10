/-
  LeanVM.Guest.B1.Whir.CRounds

  The template's fold rounds on f128, honestly: the materialized pointers and the
  `opening_round` calls, block by block.
-/

module

public import LeanVM.Guest.B1.Whir.CVal
public import LeanVM.Guest.B1.Whir.Folds

/-!
# The fold rounds, honestly

* `OsSt.Below`: the state's carried values and materializations lie below its next free value.
* `osCurS_blk`, `osMatS_blk`: a materialized pointer (the cursor; a fixed buffer's, as the plan
  says) at its values (`matVal`, `matPVal`), the base times `g^off`, the materializations kept.
* `roundRets`: what `opening_round` returns on the carried capacity, the cursor, the claim and
  its seven words (its meaning's formula); `round_meaning`: on memory holding the words at the
  cursor, `γ` at the challenges' slot and `α, β, θ` at the coefficients', with both grinds
  passing, `MeaningOpeningRound` holds at it.
* `osRound_complete`: one round at its values (`osRoundF`); `osRounds_complete`: `n` of them
  (`roundsF`), the sponge, cursor and claim after them (`roundsTr`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The state below its next free value -/

/-- The state's carried values and materializations lie below its next free value. -/
structure OsSt.Below (st : OsSt) : Prop where
  fs : ∀ f ∈ st.fs, f < st.k
  cb : st.cb < st.k
  claim : st.claim < st.k
  mats : MatsBelow st.k st.mats

/-- The carried capacity's values. -/
def OsSt.fsv (σ : Val) (st : OsSt) : List E := st.fs.map fun i ↦ σ (.n i)

theorem OsSt.agree {st : OsSt} (hb : st.Below) {σ σ' : Val} (ha : AgreeBelow st.k σ σ') :
    st.fsv σ' = st.fsv σ ∧ st.F σ' = st.F σ ∧ σ' (.n st.claim) = σ (.n st.claim) ∧
      st.cur σ' = st.cur σ := by
  have hfsv : st.fsv σ' = st.fsv σ :=
    List.map_congr_left fun f hf ↦ ha f (hb.fs f hf)
  refine ⟨hfsv, ?_, ha _ hb.claim, ?_⟩
  · simp only [OsSt.F]; exact congrArg (fun l ↦ (⟨l, []⟩ : Fs)) hfsv
  · simp only [OsSt.cur, ha _ hb.cb]

/-! ## Materialized pointers -/

/-- The values of `osMat base off k`. -/
def matVal (σ : Val) (base off k i : ℕ) : E :=
  if i = k then gw off else σ (.n base) * gw off

/-- The values of `osMatP plan mats base off k`. -/
def matPVal (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) (σ : Val) (i : ℕ) : E :=
  if i = k then gw (osMatSD plan mats base off).2
  else σ (.n (osMatSD plan mats base off).1) * gw (osMatSD plan mats base off).2

/-- **The cursor, materialized.** -/
theorem osCurS_blk {st : OsSt} (σ : Val) (hb : st.cb < st.k) (hco : st.co < u128Bound) :
    BlkF C rd σ st.k (osCurS st).2.2.k (matVal σ st.cb st.co st.k) (osCurS st).1
      (fun σ' ↦ σ' (.n (osCurS st).2.1) = σ (.n st.cb) * gen ^ st.co) := by
  intro σ' ha hv
  by_cases h0 : st.co = 0
  · simp only [osCurS, osMat, h0, ↓reduceIte, pow_zero, mul_one]
    exact ⟨allOk_nil, ha _ hb⟩
  · simp only [osCurS, osMat, h0, ↓reduceIte] at hv ⊢
    have e0 := hv st.k le_rfl (by omega)
    have e1 := hv (st.k + 1) (by omega) (by omega)
    simp only [matVal, ↓reduceIte, show st.k + 1 ≠ st.k by omega] at e0 e1
    refine ⟨?_, by rw [e1, gw_eq hco]⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨e0, by rw [e1, e0, ha _ hb]⟩

theorem osCurS_k (st : OsSt) : st.k ≤ (osCurS st).2.2.k := osMat_next _ _ _

/-- **A fixed buffer's pointer, materialized as the plan says**: the base times `g^off`, the
materializations kept. -/
theorem osMatS_blk {P : List (ℕ × ℕ × ℕ)} {base off : ℕ} {s : OsSt} (σ : Val)
    (hbase : base < s.k) (hmb : MatsBelow s.k s.mats) (hm : MatsOk σ s.mats) (hoff : off < u128Bound) :
    BlkF C rd σ s.k (osMatS P base off s).2.2.k (matPVal P s.mats base off s.k σ) (osMatS P base off s).1
      (fun σ' ↦ σ' (.n (osMatS P base off s).2.1) = σ (.n base) * gen ^ off ∧
        MatsOk σ' (osMatS P base off s).2.2.mats ∧
        MatsBelow (osMatS P base off s).2.2.k (osMatS P base off s).2.2.mats) := by
  intro σ' ha hv
  have hm' : MatsOk σ' s.mats := matsOk_agree hm hmb fun i hi ↦ ha i hi
  have hsrc := osMatSD_lt (plan := P) (off := off) hmb hbase
  have hok : AllOk C rd σ' (osMatS P base off s).1 := by
    by_cases h0 : off = 0
    · simp only [osMatS, osMatP, h0, ↓reduceIte]; exact allOk_nil
    · simp only [osMatS]
      rw [osMatP_eq s.k h0]
      have hk : (osMatS P base off s).2.2.k = s.k + 2 := by
        simp only [osMatS, (osMatP_shape P s.mats base off s.k).2 h0]
      rw [hk] at hv
      have e0 := hv s.k le_rfl (by omega)
      have e1 := hv (s.k + 1) (by omega) (by omega)
      simp only [matPVal, ↓reduceIte, show s.k + 1 ≠ s.k by omega] at e0 e1
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨e0, by rw [e1, e0, ha _ hsrc]⟩
  refine ⟨hok, ?_, osMatsAfter_ok hm' hoff hok, ?_⟩
  · have := osMatP_val hm' hoff hok
    simp only [osMatS] at this ⊢
    rw [this, ha _ hbase]
  · by_cases h0 : off = 0
    · simp only [osMatS, osMatsAfter, osMatP, h0, ↓reduceIte]; exact hmb
    · have hk : (osMatS P base off s).2.2.k = s.k + 2 := by
        simp only [osMatS, (osMatP_shape P s.mats base off s.k).2 h0]
      rw [hk]
      exact matsBelow_after hmb hbase (by omega) (by omega)

theorem osMatS_k (P : List (ℕ × ℕ × ℕ)) (base off : ℕ) (s : OsSt) :
    s.k ≤ (osMatS P base off s).2.2.k := osMatP_next _ _ _ _ _

/-! ## One round -/

/-- `opening_round`'s returns on the capacity `fs`, the cursor, the claim and its seven words. -/
def roundRets (fs : List E) (cur claim : E) (xs : List E) : List E :=
  let n1 := xs.getD 0 0
  let m := [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0]
  let n2 := xs.getD 6 0
  let ga := (rdG2 fs n1 m n2).2.squeeze
  let gb := ga.2.squeeze
  gb.2.cap ++ [cur * gen ^ 7, roundClaim claim (rdG1 fs n1).1 (rdG2 fs n1 m n2).1 ga.1 gb.1
    (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 4 0) (xs.getD 5 0)]

/-- The round's `γ`, `α`, `β`, `θ`. -/
def roundChs (fs xs : List E) : E × E × E × E :=
  let n1 := xs.getD 0 0
  let m := [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0]
  let n2 := xs.getD 6 0
  ((rdG2 fs n1 m n2).1, (rdG2 fs n1 m n2).2.squeeze.1, (rdG2 fs n1 m n2).2.squeeze.2.squeeze.1,
    (rdG1 fs n1).1)

/-- Both grinds of a round pass. -/
def RoundGrinds (fs xs : List E) : Prop :=
  (⟨fs, []⟩ : Fs).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits (xs.getD 0 0) ∧
    (rdS2 fs (xs.getD 0 0) [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0]).GrindOk
      _root_.LeanVM.Parameters.Whir.foldGrindingBits (xs.getD 6 0)

/-- **`opening_round`'s meaning at its returns**, on memory holding its words, its challenges'
slots and its grinds passing. -/
theorem round_meaning {f0 f1 f2 f3 f4 cur claim tabs gp cp : E} {xs : List E} (hxl : xs.length = 7)
    (hrd : ReadsAt rd cur xs) (hg : RoundGrinds [f0, f1, f2, f3, f4] xs)
    (hγ : LoadHolds rd gp 0 (roundChs [f0, f1, f2, f3, f4] xs).1)
    (hα : LoadHolds rd cp 0 (roundChs [f0, f1, f2, f3, f4] xs).2.1)
    (hβ : LoadHolds rd cp 1 (roundChs [f0, f1, f2, f3, f4] xs).2.2.1)
    (hθ : LoadHolds rd cp 2 (roundChs [f0, f1, f2, f3, f4] xs).2.2.2) :
    MeaningOpeningRound rd [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp]
      (roundRets [f0, f1, f2, f3, f4] cur claim xs) := by
  obtain ⟨n1, u0, v0, c0, v1, c1, n2, rfl⟩ : ∃ n1 u0 v0 c0 v1 c1 n2, xs = [n1, u0, v0, c0, v1, c1, n2] := by
    match xs, hxl with
    | [a, b, c, d, e, f, g], _ => exact ⟨a, b, c, d, e, f, g, rfl⟩
  exact ⟨n1, u0, v0, c0, v1, c1, n2, hrd, hg.1, hg.2, hγ, hα, hβ, hθ, rfl⟩

theorem osMat_ptr_lt (base off k : ℕ) (hb : base < k) : (osMat base off k).2.1 < (osMat base off k).2.2 := by
  unfold osMat; split_ifs <;> dsimp only <;> omega

theorem osMatS_ptr_lt (P : List (ℕ × ℕ × ℕ)) (base off : ℕ) (s : OsSt) (hb : base < s.k) :
    (osMatS P base off s).2.1 < (osMatS P base off s).2.2.k := by
  simp only [osMatS, osMatP]; split_ifs <;> dsimp only <;> omega

/-- The sponge after a round. -/
def roundF (fs : List E) (cur claim : E) (xs : List E) : Fs := ⟨(roundRets fs cur claim xs).take 5, []⟩

/-- What a round leaves. -/
structure RoundOut (σ σ' : Val) (st st' : OsSt) (xs : List E) : Prop where
  F : st'.F σ' = roundF (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs
  cur : st'.cur σ' = st.cur σ * gen ^ 7
  claim : σ' (.n st'.claim) = (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs).getD 6 0
  fs : st'.fs.length = 5
  co : st'.co = 0
  below : st'.Below
  mats : MatsOk σ' st'.mats
  pad : st'.pad = st.pad

/-- The values of one round. -/
def osRoundF (P : List (ℕ × ℕ × ℕ)) (i : ℕ) (st : OsSt) (xs : List E) (σ : Val) : ℕ → E :=
  let cu := osCurS st
  let fp := osMatS P osFch i cu.2.2
  let cp := osMatS P osCoefs (3 * i) fp.2.2
  seqF σ st.k cp.2.2.k
    (seqF σ st.k fp.2.2.k (seqF σ st.k cu.2.2.k (matVal σ st.cb st.co st.k)
      (fun σ1 ↦ matPVal P cu.2.2.mats osFch i cu.2.2.k σ1))
      (fun σ2 ↦ matPVal P fp.2.2.mats osCoefs (3 * i) fp.2.2.k σ2))
    (fun _ j ↦ (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs).getD (j - cp.2.2.k) 0)

/-- **One round, honestly.** -/
theorem osRound_complete {P : List (ℕ × ℕ × ℕ)} {i : ℕ} {st : OsSt} (σ : Val) (xs : List E)
    (hco : st.co < u128Bound) (hi : 3 * i < u128Bound) (hb : st.Below)
    (hm : MatsOk σ st.mats) (hk : 36 ≤ st.k)
    (hC : C "opening_round" (st.fsv σ ++ [st.cur σ, σ (.n st.claim), σ (.n osTabs),
      σ (.n osFch) * gen ^ i, σ (.n osCoefs) * gen ^ (3 * i)])
      (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs)) :
    BlkF C rd σ st.k (osRound P i st).2.k (osRoundF P i st xs σ) (osRound P i st).1
      (fun σ' ↦ RoundOut σ σ' st (osRound P i st).2 xs ∧ AgreeBelow st.k σ σ') := by
  set cu := osCurS st with hcu
  set fp := osMatS P osFch i cu.2.2 with hfp
  set cp := osMatS P osCoefs (3 * i) fp.2.2 with hcp
  have k1 : st.k ≤ cu.2.2.k := osCurS_k st
  have k2 : cu.2.2.k ≤ fp.2.2.k := osMatS_k _ _ _ _
  have k3 : fp.2.2.k ≤ cp.2.2.k := osMatS_k _ _ _ _
  have hcuk : cu.2.2.mats = st.mats := rfl
  have hi1 : i < u128Bound := lt_of_le_of_lt (by omega) hi
  have hA := osCurS_blk (C := C) (rd := rd) σ hb.cb hco
  have hmb1 : MatsBelow cu.2.2.k cu.2.2.mats := fun m hm' ↦ by
    obtain ⟨a, b, c⟩ := hb.mats m hm'; exact ⟨by omega, by omega, by omega⟩
  have h12 := BlkF.seq k1 k2 hA (OutB := fun σ' ↦ σ' (.n fp.2.1) = σ (.n osFch) * gen ^ i ∧
      MatsOk σ' fp.2.2.mats ∧ MatsBelow fp.2.2.k fp.2.2.mats) fun σ1 ha1 _ ↦
    BlkF.mono (osMatS_blk (C := C) (rd := rd) (P := P) (base := osFch) (off := i) (s := cu.2.2) σ1
      (by show 19 < cu.2.2.k; omega) hmb1 (by rw [hcuk]; exact matsOk_agree hm hb.mats ha1) hi1)
      fun σ' h ↦ by rw [ha1 _ (by show 19 < st.k; omega)] at h; exact h
  have h123 := BlkF.seq (le_trans k1 k2) k3 h12 (OutB := fun σ' ↦
      σ' (.n cp.2.1) = σ (.n osCoefs) * gen ^ (3 * i) ∧
      MatsOk σ' cp.2.2.mats ∧ MatsBelow cp.2.2.k cp.2.2.mats) fun σ2 ha2 ho2 ↦
    BlkF.mono (osMatS_blk (C := C) (rd := rd) (P := P) (base := osCoefs) (off := 3 * i) (s := fp.2.2)
      σ2 (by show 21 < fp.2.2.k; omega) ho2.2.2.2 ho2.2.2.1 hi)
      fun σ' h ↦ by rw [ha2 _ (by show 21 < st.k; omega)] at h; exact h
  have hall := BlkF.seq (le_trans (le_trans k1 k2) k3) (by show cp.2.2.k ≤ cp.2.2.k + 7; omega)
    h123 (fB := fun _ j ↦ (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs).getD (j - cp.2.2.k) 0)
    (B := [.call "opening_round" ((st.fs ++ [cu.2.1, st.claim, osTabs, fp.2.1, cp.2.1]).map V.n)
      (osRun cp.2.2.k 7)])
    (OutB := fun σ' ↦ ∀ j < 7, σ' (.n (cp.2.2.k + j)) =
      (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs).getD j 0) fun σ3 ha3 ho3 ↦ by
    intro σ' ha hv
    have hv' : ∀ j < 7, σ' (.n (cp.2.2.k + j)) =
        (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs).getD j 0 := fun j hj ↦ by
      rw [hv _ (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left]
    refine ⟨?_, hv'⟩
    obtain ⟨⟨hcur, hfpv, -⟩, hcpv, -⟩ := ho3
    have pcu : cu.2.1 < cp.2.2.k := lt_of_lt_of_le (osMat_ptr_lt _ _ _ hb.cb) (le_trans k2 k3)
    have pfp : fp.2.1 < cp.2.2.k := lt_of_lt_of_le (osMatS_ptr_lt _ _ _ _ (by show 19 < cu.2.2.k; omega)) k3
    have pcp : cp.2.1 < cp.2.2.k := osMatS_ptr_lt _ _ _ _ (by show 21 < fp.2.2.k; omega)
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_call]
    have eargs : ((st.fs ++ [cu.2.1, st.claim, osTabs, fp.2.1, cp.2.1]).map V.n).map σ' =
        st.fsv σ ++ [st.cur σ, σ (.n st.claim), σ (.n osTabs), σ (.n osFch) * gen ^ i,
          σ (.n osCoefs) * gen ^ (3 * i)] := by
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, OsSt.fsv]
      congr 1
      · exact List.map_congr_left fun f hf ↦ by
          simp only [Function.comp]
          rw [ha f (by have := hb.fs f hf; omega), ha3 f (hb.fs f hf)]
      · have pcl : st.claim < cp.2.2.k := by have := hb.claim; omega
        rw [ha _ pcu, hcur, ha _ pfp, hfpv, ha _ pcp, hcpv, ha st.claim pcl, ha3 _ hb.claim,
          ha osTabs (by show 9 < cp.2.2.k; omega), ha3 osTabs (by show 9 < st.k; omega)]
        rfl
    rw [eargs]
    have erets : (osRun cp.2.2.k 7).map σ' = roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs := by
      refine List.ext_getElem (by simp [osRun, roundRets, Fs.squeeze, capOf]) fun j h1 h2 ↦ ?_
      simp only [osRun, List.length_map, List.length_range] at h1
      simp only [osRun, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
      rw [hv' j h1, List.getD_eq_getElem _ _ h2]
    rw [erets]
    exact hC
  intro σ' ha hv
  obtain ⟨hok, ⟨⟨-, -⟩, -, hcpm, hcpb⟩, hret⟩ := hall σ' ha hv
  refine ⟨hok, ?_, ha⟩
  have lr : (roundRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) xs).length = 7 := by
    simp [roundRets, Fs.squeeze, capOf]
  have ek : (osRound P i st).2.k = cp.2.2.k + 7 := rfl
  have efs : (osRound P i st).2.fs = [cp.2.2.k, cp.2.2.k + 1, cp.2.2.k + 2, cp.2.2.k + 3,
      cp.2.2.k + 4] := rfl
  have ecb : (osRound P i st).2.cb = cp.2.2.k + 5 := rfl
  have eco : (osRound P i st).2.co = 0 := rfl
  have ecl : (osRound P i st).2.claim = cp.2.2.k + 6 := rfl
  have emats : (osRound P i st).2.mats = cp.2.2.mats := rfl
  refine ⟨?_, ?_, by rw [ecl]; exact hret 6 (by omega), by rw [efs]; rfl, eco,
    ⟨?_, ?_, ?_, ?_⟩, by rw [emats]; exact hcpm, rfl⟩
  · simp only [OsSt.F, efs, roundF, List.map_cons, List.map_nil]
    congr 1
    refine List.ext_getElem (by simp [lr]) fun j h1 h2 ↦ ?_
    simp only [List.length_cons, List.length_nil] at h1
    rw [List.getElem_take]
    have := hret j (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    interval_cases j <;> simpa using this
  · simp only [OsSt.cur, ecb, eco, pow_zero, mul_one]
    have := hret 5 (by omega)
    simp only [roundRets, Fs.squeeze, capOf, List.cons_append, List.nil_append, List.getD_cons_succ,
      List.getD_cons_zero] at this
    rw [this]; rfl
  · intro f hf
    rw [efs] at hf
    rw [ek]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [ecb, ek]; omega
  · rw [ecl, ek]; omega
  · intro m hm'
    rw [emats] at hm'
    obtain ⟨a, b, c⟩ := hcpb m hm'
    rw [ek]
    exact ⟨by omega, by omega, by omega⟩
/-! ## The rounds -/

/-- **The honest rounds**: from the capacity `fs` and the claim `cl`, on the words `xs`, `n`
rounds' capacity and claim. -/
def roundsTr : ℕ → List E → E → List E → List E × E
  | 0, fs, cl, _ => (fs, cl)
  | n + 1, fs, cl, xs =>
    roundsTr n ((roundRets fs 0 cl (xs.take 7)).take 5) ((roundRets fs 0 cl (xs.take 7)).getD 6 0)
      (xs.drop 7)

/-- What the memory holds for `n` rounds from `i`: each round's grinds pass, its `γ` at
`fch·g^i`, its `α, β, θ` at `coefs·g^(3i)`. -/
def RoundsMem (rd : Reader) (fch coefs : E) : ℕ → ℕ → List E → E → List E → Prop
  | 0, _, _, _, _ => True
  | n + 1, i, fs, cl, xs =>
    RoundGrinds fs (xs.take 7) ∧
      LoadHolds rd (fch * gen ^ i) 0 (roundChs fs (xs.take 7)).1 ∧
      LoadHolds rd (coefs * gen ^ (3 * i)) 0 (roundChs fs (xs.take 7)).2.1 ∧
      LoadHolds rd (coefs * gen ^ (3 * i)) 1 (roundChs fs (xs.take 7)).2.2.1 ∧
      LoadHolds rd (coefs * gen ^ (3 * i)) 2 (roundChs fs (xs.take 7)).2.2.2 ∧
      RoundsMem rd fch coefs n (i + 1) ((roundRets fs 0 cl (xs.take 7)).take 5)
        ((roundRets fs 0 cl (xs.take 7)).getD 6 0) (xs.drop 7)

theorem roundRets_take (fs : List E) (cur cur' cl : E) (xs : List E) :
    (roundRets fs cur cl xs).take 5 = (roundRets fs cur' cl xs).take 5 := by
  simp [roundRets, Fs.squeeze, capOf]

theorem roundRets_claim (fs : List E) (cur cur' cl : E) (xs : List E) :
    (roundRets fs cur cl xs).getD 6 0 = (roundRets fs cur' cl xs).getD 6 0 := by
  simp [roundRets, Fs.squeeze, capOf]

/-- What the rounds leave. -/
structure RoundsOut (σ σ' : Val) (st st' : OsSt) (r : List E × E) (n : ℕ) : Prop where
  F : st'.F σ' = ⟨r.1, []⟩
  cur : st'.cur σ' = st.cur σ * gen ^ (7 * n)
  claim : σ' (.n st'.claim) = r.2
  fs : st'.fs.length = 5
  co : st'.co < u128Bound
  below : st'.Below
  mats : MatsOk σ' st'.mats
  pad : st'.pad = st.pad
  k : st.k ≤ st'.k

theorem osRound_k (P : List (ℕ × ℕ × ℕ)) (i : ℕ) (st : OsSt) : st.k ≤ (osRound P i st).2.k := by
  have := osCurS_k st
  have := osMatS_k P osFch i (osCurS st).2.2
  have := osMatS_k P osCoefs (3 * i) (osMatS P osFch i (osCurS st).2.2).2.2
  show st.k ≤ _ + 7
  omega

theorem osRounds_k (P : List (ℕ × ℕ × ℕ)) : ∀ (n i : ℕ) (st : OsSt), st.k ≤ (osRounds P i n st).2.k
  | 0, _, _ => le_rfl
  | n + 1, i, st => le_trans (osRound_k P i st) (osRounds_k P n (i + 1) _)

/-- The values of `n` rounds from `i`. -/
def roundsF (P : List (ℕ × ℕ × ℕ)) : ℕ → ℕ → OsSt → List E → Val → ℕ → E
  | 0, _, _, _, _ => fun _ ↦ 0
  | n + 1, i, st, xs, σ =>
    seqF σ st.k (osRound P i st).2.k (osRoundF P i st (xs.take 7) σ)
      (fun σ1 ↦ roundsF P n (i + 1) (osRound P i st).2 (xs.drop 7) σ1)

/-- **`n` rounds, honestly.** -/
theorem osRounds_complete {P : List (ℕ × ℕ × ℕ)}
    (hC : ∀ a r, MeaningOpeningRound rd a r → C "opening_round" a r) :
    ∀ (n i : ℕ) (st : OsSt) (σ : Val) (xs : List E), st.co < u128Bound → 3 * (i + n) < u128Bound →
      st.Below → MatsOk σ st.mats → 36 ≤ st.k → st.fs.length = 5 → xs.length = 7 * n →
      ReadsAt rd (st.cur σ) xs →
      RoundsMem rd (σ (.n osFch)) (σ (.n osCoefs)) n i (st.fsv σ) (σ (.n st.claim)) xs →
      BlkF C rd σ st.k (osRounds P i n st).2.k (roundsF P n i st xs σ) (osRounds P i n st).1
        (fun σ' ↦ RoundsOut σ σ' st (osRounds P i n st).2
          (roundsTr n (st.fsv σ) (σ (.n st.claim)) xs) n ∧ AgreeBelow st.k σ σ') := by
  intro n
  induction n with
  | zero =>
    intro i st σ xs hco _ hb hm _ hfs _ _ _
    rw [show osRounds P i 0 st = ([], st) from rfl]
    refine BlkF.nil fun σ' ha ↦ ⟨?_, ha⟩
    obtain ⟨e1, e2, e3, e4⟩ := OsSt.agree hb ha
    exact ⟨by rw [e2]; rfl, by rw [e4]; simp, e3, hfs, hco, hb,
      matsOk_agree hm hb.mats fun i hi ↦ ha i hi, rfl, le_rfl⟩
  | succ n ih =>
    intro i st σ xs hco hi hb hm hk hfs hxl hrd hmem
    obtain ⟨hg, lg, la, lb, lt, hmem'⟩ := hmem
    have hx7 : (xs.take 7).length = 7 := by simp [hxl]
    have hrd0 : ReadsAt rd (st.cur σ) (xs.take 7) := fun j hj ↦ by
      have := hrd j (by simp at hj; omega)
      simpa [List.getElem_take] using this
    have hrd1 : ReadsAt rd (st.cur σ * gen ^ 7) (xs.drop 7) := fun j hj ↦ by
      have := hrd (j + 7) (by simp at hj; omega)
      rw [loadHolds_mul_gen_pow, show 7 + j = j + 7 by ring]
      simpa [Nat.add_comm] using this
    obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
    have hfsv : st.fsv σ = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
      simp [OsSt.fsv, hf]
    rw [hfsv] at hg lg la lb lt
    rw [loadHolds_mul_gen_pow, Nat.add_zero] at lg la
    rw [loadHolds_mul_gen_pow] at lb lt
    have hA := osRound_complete (C := C) (rd := rd) (P := P) (i := i) σ (xs.take 7) hco
      (by omega) hb hm hk (by
        rw [hfsv]
        refine hC _ _ (round_meaning hx7 hrd0 hg ?_ ?_ ?_ ?_)
        · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lg
        · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact la
        · rw [loadHolds_mul_gen_pow]; exact lb
        · rw [loadHolds_mul_gen_pow]; exact lt)
    set st1 := (osRound P i st).2 with hst1
    have hk1 : st.k ≤ st1.k := osRound_k P i st
    have hk2 : st1.k ≤ (osRounds P (i + 1) n st1).2.k := osRounds_k P n (i + 1) st1
    have e : osRounds P i (n + 1) st = ((osRound P i st).1 ++ (osRounds P (i + 1) n st1).1,
        (osRounds P (i + 1) n st1).2) := rfl
    rw [e]
    set w := xs.take 7 with hw
    set fsv := st.fsv σ with hfsv'
    set cl := σ (.n st.claim) with hcl
    have hR : roundsTr (n + 1) fsv cl xs =
        roundsTr n ((roundRets fsv 0 cl w).take 5) ((roundRets fsv 0 cl w).getD 6 0) (xs.drop 7) :=
      rfl
    have hB : ∀ σ1, AgreeBelow st.k σ σ1 → (RoundOut σ σ1 st st1 w ∧ AgreeBelow st.k σ σ1) →
        BlkF C rd σ1 st1.k (osRounds P (i + 1) n st1).2.k (roundsF P n (i + 1) st1 (xs.drop 7) σ1)
          (osRounds P (i + 1) n st1).1
          (fun σ' ↦ RoundsOut σ σ' st (osRounds P (i + 1) n st1).2
            (roundsTr (n + 1) fsv cl xs) (n + 1)) := by
      intro σ1 _ ⟨ro, ha1⟩
      have ef : st1.fsv σ1 = (roundRets fsv 0 cl w).take 5 := by
        have := congrArg Fs.cap ro.F
        simp only [OsSt.F, roundF] at this
        rw [roundRets_take _ _ 0] at this
        exact this
      have ec : σ1 (.n st1.claim) = (roundRets fsv 0 cl w).getD 6 0 := by
        rw [ro.claim, roundRets_claim _ _ 0]
      have hih := ih (i + 1) st1 σ1 (xs.drop 7) (by rw [ro.co]; unfold u128Bound; positivity)
        (by omega) ro.below ro.mats (le_trans hk hk1) ro.fs (by simp [hxl]; omega)
        (by rw [ro.cur]; exact hrd1) (by
          rw [ef, ec, ha1 osFch (by show 19 < st.k; omega), ha1 osCoefs (by show 21 < st.k; omega)]
          exact hmem')
      rw [ef, ec, ← hR] at hih
      refine BlkF.mono hih fun σ' ⟨ho, _⟩ ↦ ⟨ho.F, ?_, ho.claim, ho.fs, ho.co, ho.below, ho.mats,
        by rw [ho.pad, ro.pad], le_trans hk1 ho.k⟩
      rw [ho.cur, ro.cur, mul_assoc, ← pow_add]
      ring_nf
    exact BlkF.mono (BlkF.seq hk1 hk2 hA hB) fun σ' ⟨⟨_, ha'⟩, ho⟩ ↦ ⟨ho, ha'⟩

end
end LeanVM.Guest.B1.Whir
