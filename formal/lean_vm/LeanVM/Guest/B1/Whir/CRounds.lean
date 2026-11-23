/-
  LeanVM.Guest.B1.Whir.CRounds

  The template's fold rounds, honestly: the materialized pointers, the rounds' honest returns and
  what the memory holds for them.
-/

module

public import LeanVM.Guest.B1.Whir.CVal
public import LeanVM.Guest.B1.Whir.Folds

/-!
# The fold rounds, honestly

* `OsSt.Below`: the state's carried values and materializations lie below its next free value.
* `osCurS_blk`, `osMatS_blk`: a materialized pointer (the cursor; a fixed buffer's, as the plan
  says) at its values (`matVal`, `matPVal`), the base times `g^off`, the materializations kept.
* `roundRets`: what a fold round returns on the carried capacity, the cursor, the claim and its
  five words (`opening_round`'s meaning's formula); `round_meaning`: on memory holding the words at
  the cursor, `α` at the challenges' slot and `α, β` at the coefficients', with the grind passing,
  `MeaningOpeningRound` holds at it.
* `roundsTr`: the capacity and claim after `n` rounds; `RoundsMem`: what the memory holds for them;
  `RoundsOut`: what they leave (`Whir/CRoundsA` proves the inline rounds).
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

/-- A fold round's returns (`opening_round`, inline) on the capacity `fs`, the cursor, the claim and its five words. -/
def roundRets (fs : List E) (cur claim : E) (xs : List E) : List E :=
  let m := [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0]
  let n2 := xs.getD 4 0
  let ga := rdG2 fs m n2
  let gb := ga.2.squeeze
  gb.2.cap ++ [cur * gen ^ 5, roundClaim claim ga.1 gb.1
    (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0)]

/-- The round's point coordinate `α`, then its `α`, `β`. -/
def roundChs (fs xs : List E) : E × E × E :=
  let m := [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0]
  let n2 := xs.getD 4 0
  ((rdG2 fs m n2).1, (rdG2 fs m n2).1, (rdG2 fs m n2).2.squeeze.1)

/-- The round's grind passes. -/
def RoundGrinds (fs xs : List E) : Prop :=
  (rdS2 fs [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0]).GrindOk
    _root_.LeanVM.Parameters.Whir.foldGrindingBits (xs.getD 4 0)

/-- **`opening_round`'s meaning at its returns**, on memory holding its words, its challenges'
slots and its grind passing. -/
theorem round_meaning {f0 f1 f2 f3 f4 cur claim tabs gp cp : E} {xs : List E} (hxl : xs.length = 5)
    (hrd : ReadsAt rd cur xs) (hg : RoundGrinds [f0, f1, f2, f3, f4] xs)
    (hγ : LoadHolds rd gp 0 (roundChs [f0, f1, f2, f3, f4] xs).1)
    (hα : LoadHolds rd cp 0 (roundChs [f0, f1, f2, f3, f4] xs).2.1)
    (hβ : LoadHolds rd cp 1 (roundChs [f0, f1, f2, f3, f4] xs).2.2) :
    MeaningOpeningRound rd [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp]
      (roundRets [f0, f1, f2, f3, f4] cur claim xs) := by
  obtain ⟨u0, w, c0, c1, n2, rfl⟩ : ∃ u0 w c0 c1 n2, xs = [u0, w, c0, c1, n2] := by
    match xs, hxl with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  exact ⟨u0, w, c0, c1, n2, hrd, hg, hγ, hα, hβ, rfl⟩

theorem osMat_ptr_lt (base off k : ℕ) (hb : base < k) : (osMat base off k).2.1 < (osMat base off k).2.2 := by
  unfold osMat; split_ifs <;> dsimp only <;> omega

theorem osMatS_ptr_lt (P : List (ℕ × ℕ × ℕ)) (base off : ℕ) (s : OsSt) (hb : base < s.k) :
    (osMatS P base off s).2.1 < (osMatS P base off s).2.2.k := by
  simp only [osMatS, osMatP]; split_ifs <;> dsimp only <;> omega

/-! ## The rounds -/

/-- **The honest rounds**: from the capacity `fs` and the claim `cl`, on the words `xs`, `n`
rounds' capacity and claim. -/
def roundsTr : ℕ → List E → E → List E → List E × E
  | 0, fs, cl, _ => (fs, cl)
  | n + 1, fs, cl, xs =>
    roundsTr n ((roundRets fs 0 cl (xs.take 5)).take 5) ((roundRets fs 0 cl (xs.take 5)).getD 6 0)
      (xs.drop 5)

/-- What the memory holds for `n` rounds from `i`: each round's grind passes, its `α` at
`fch·g^i`, its `α, β` at `coefs·g^(2i)`. -/
def RoundsMem (rd : Reader) (fch coefs : E) : ℕ → ℕ → List E → E → List E → Prop
  | 0, _, _, _, _ => True
  | n + 1, i, fs, cl, xs =>
    RoundGrinds fs (xs.take 5) ∧
      LoadHolds rd (fch * gen ^ i) 0 (roundChs fs (xs.take 5)).1 ∧
      LoadHolds rd (coefs * gen ^ (2 * i)) 0 (roundChs fs (xs.take 5)).2.1 ∧
      LoadHolds rd (coefs * gen ^ (2 * i)) 1 (roundChs fs (xs.take 5)).2.2 ∧
      RoundsMem rd fch coefs n (i + 1) ((roundRets fs 0 cl (xs.take 5)).take 5)
        ((roundRets fs 0 cl (xs.take 5)).getD 6 0) (xs.drop 5)

/-- What the rounds leave. -/
structure RoundsOut (σ σ' : Val) (st st' : OsSt) (r : List E × E) (n : ℕ) : Prop where
  F : st'.F σ' = ⟨r.1, []⟩
  cur : st'.cur σ' = st.cur σ * gen ^ (5 * n)
  claim : σ' (.n st'.claim) = r.2
  fs : st'.fs.length = 5
  co : st'.co = st.co + 5 * n
  below : st'.Below
  mats : MatsOk σ' st'.mats
  pad : st'.pad = st.pad
  k : st.k ≤ st'.k

end
end LeanVM.Guest.B1.Whir
