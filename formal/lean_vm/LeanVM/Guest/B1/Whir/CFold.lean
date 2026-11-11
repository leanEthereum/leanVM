/-
  LeanVM.Guest.B1.Whir.CFold

  The template's sumcheck rounds, honestly: the completeness of `osFold`, `osFolds`, at a rate's
  fold grinding.
-/

module

public import LeanVM.Guest.B1.Whir.CPrim
public import LeanVM.Guest.B1.Whir.Folds

/-!
# The fold rounds, honestly

A round at `b` bits (`osFoldCall`: `opening_fold`, or the rate's `opening_fold_round`) reads its
nonce at `b > 0` and the next quadratic's two words (`powWords`, `MeaningFoldRound`).
`FoldCallC`: the round's call holds of every meaning it can have. `osFold_complete`: from the
carried sponge (canonical capacity), the round's words at the cursor, its proof of work passing
and the challenge's slot holding the challenge, the round's values make the block hold, with
`FoldOutB`. `foldsTr b`: the honest rounds; `osFolds_complete`: `n` rounds.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The state's values lie below its next free value. -/
structure OsSt.Below (st : OsSt) : Prop where
  fs : ∀ f ∈ st.fs, f < st.k
  w0 : st.w0 < st.k
  w1 : st.w1 < st.k
  cb : st.cb < st.k
  c : st.c < st.k
  b : st.b < st.k
  a : st.a < st.k
  t : st.t < st.k

/-- **The rounds' calls hold of their meaning**: at the rate's selector `R`, on canonical capacity
cells. -/
def FoldCallC (C : CallRel) (rd : Reader) (fr : Option (List String)) (b : ℕ) (R : E) : Prop :=
  ∀ σ : Val, σ (.n osRate) = R → ∀ args rets : List V, AllCanonical ((args.map σ).take 5) →
    MeaningFoldRound b rd (args.map σ) (rets.map σ) → StmtOk C rd σ (osFoldCall fr args rets)

/-- The values of one round after its pointer: the squeeze's capacity, the cursor, the claim, the
two words, the challenge, the next `b`. -/
def foldVals (σ : Val) (st : OsSt) (b : ℕ) (nonce d0 d2 : E) : List E :=
  let r := (powSponge b (st.F σ) nonce).squeeze
  let claim := (σ (.n st.a) * r.1 + σ (.n st.b)) * r.1 + σ (.n st.c)
  r.2.cap ++ [st.cur σ * gen ^ roundLen b, claim, d0, d2, r.1, claim + d2]

/-- The round's values. -/
def osFoldF (σ : Val) (st : OsSt) (b : ℕ) (nonce d0 d2 : E) (i : ℕ) : E :=
  if i < (osMat st.cb st.co st.k).2.2 then matVal σ st.cb st.co st.k i
  else (foldVals σ st b nonce d0 d2).getD (i - (osMat st.cb st.co st.k).2.2) 0

theorem powSponge_cap_length (b : ℕ) (F : Fs) (nonce : E) :
    (powSponge b F nonce).squeeze.2.cap.length = 5 := by
  simp [Fs.squeeze, capOf]

/-- **One round, honestly.** -/
theorem osFold_complete {fr : Option (List String)} {b : ℕ} {R : E} (hC : FoldCallC C rd fr b R)
    {p off : ℕ} {st : OsSt} (σ : Val) (hR : σ (.n osRate) = R) (hk0 : osRate < st.k)
    (hfs : st.fs.length = 5) (hco : st.co < u128Bound)
    (hb : st.Below) (hp : p < st.k) (hcan : AllCanonical (st.fsv σ)) {nonce d0 d2 : E}
    (hrd : ReadsAt rd (st.cur σ) (powWords b nonce ++ [d0, d2])) (hpow : PowOk b (st.F σ) nonce)
    (hst : LoadHolds rd (σ (.n p)) off (powSponge b (st.F σ) nonce).squeeze.1) :
    BlkF C rd σ st.k (osFold fr p off st).2.k (osFoldF σ st b nonce d0 d2) (osFold fr p off st).1
      (fun σ' ↦ FoldOutB σ' st (osFold fr p off st).2 b nonce d0 d2 ∧ AgreeBelow st.k σ σ') := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  intro σ' ha hv
  have hmk : st.k ≤ (osMat st.cb st.co st.k).2.2 := osMat_next _ _ _
  have hmv : RangeVals σ' st.k (osMat st.cb st.co st.k).2.2 (matVal σ st.cb st.co st.k) :=
    fun i h1 h2 ↦ by
      rw [hv i h1 (by simp only [osFold]; omega)]
      simp only [osFoldF, h2, ↓reduceIte]
  obtain ⟨okm, hcur⟩ := osMat_complete (C := C) (rd := rd) hco hb.cb ha hmv
  have hval : ∀ j < 11, σ' (.n ((osMat st.cb st.co st.k).2.2 + j)) =
      (foldVals σ st b nonce d0 d2).getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by simp only [osFold]; omega)]
    simp only [osFoldF, show ¬ ((osMat st.cb st.co st.k).2.2 + j < (osMat st.cb st.co st.k).2.2)
      by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  set r := (osMat st.cb st.co st.k).2.2 with hr
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
      [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve)]⟩ := by
    simp [OsSt.F, OsSt.fsv, hf]
  have hfl : ∀ f ∈ st.fs, f < st.k := hb.fs
  rw [hf] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  have v : ∀ j, j < 11 → σ' (.n (r + j)) = _ := hval
  simp only [foldVals, List.getD_eq_getElem?_getD] at v
  set S := (powSponge b (st.F σ) nonce).squeeze with hS
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ : ∃ c0 c1 c2 c3 c4, S.2.cap = [c0, c1, c2, c3, c4] := by
    have hcap : S.2.cap.length = 5 := powSponge_cap_length b _ nonce
    match h : S.2.cap, hcap with
    | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
  rw [hc] at v
  have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
  have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
  have v6 := v 6 (by omega); have v7 := v 7 (by omega); have v8 := v 8 (by omega)
  have v9 := v 9 (by omega); have v10 := v 10 (by omega)
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  have hagree : ∀ i < st.k, σ' (.n i) = σ (.n i) := ha
  have hFe : OsSt.F σ' st = OsSt.F σ st := by
    simp only [OsSt.F, OsSt.fsv, hf, List.map_cons, List.map_nil, hagree f0 hfl.1,
      hagree f1 hfl.2.1, hagree f2 hfl.2.2.1, hagree f3 hfl.2.2.2.1, hagree f4 hfl.2.2.2.2,
      hagree st.w0 hb.w0, hagree st.w1 hb.w1]
  have hCe : OsSt.cur σ' st = OsSt.cur σ st := by simp only [OsSt.cur, hagree st.cb hb.cb]
  have hRe : σ' (.n osRate) = R := by rw [hagree _ hk0, hR]
  refine ⟨?_, ⟨by simp [osFold], ?_, ?_, ?_, ?_⟩, ha⟩
  · simp only [osFold]
    rw [allOk_append]
    refine ⟨okm, ?_⟩
    rw [allOk_cons]
    refine ⟨hC σ' hRe _ _ ?_ ?_, ?_⟩
    · simp only [hf, List.cons_append, List.nil_append, List.map_cons, List.take_succ_cons,
        List.take_zero]
      rw [hagree f0 hfl.1, hagree f1 hfl.2.1, hagree f2 hfl.2.2.1, hagree f3 hfl.2.2.2.1,
        hagree f4 hfl.2.2.2.2]
      simpa [OsSt.fsv, hf] using hcan
    · simp only [hf, List.cons_append, List.nil_append, List.map_cons, List.map_nil, osRun,
        List.range_succ, List.range_zero, Nat.add_zero]
      rw [hagree f0 hfl.1, hagree f1 hfl.2.1, hagree f2 hfl.2.2.1, hagree f3 hfl.2.2.2.1,
        hagree f4 hfl.2.2.2.2, hagree st.w0 hb.w0, hagree st.w1 hb.w1, hcur, hagree st.c hb.c,
        hagree st.b hb.b, hagree st.a hb.a, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
      refine ⟨nonce, d0, d2, by simpa [OsSt.cur] using hrd, by rw [← hF]; exact hpow, ?_⟩
      rw [← hF, ← hS]
      dsimp only
      rw [hc]
      simp only [OsSt.cur, List.cons_append, List.nil_append]
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨by rw [v9, hagree p hp]; exact hst, by rw [v10, v6, v8]⟩
  · rw [hFe, ← hS]
    simp only [OsSt.F, OsSt.fsv, osFold, List.map_cons, List.map_nil]
    rw [v0, v1, v2, v3, v4, v7, v8, ← hc]
  · rw [hCe]
    simp only [OsSt.cur, osFold, pow_zero, mul_one]
    rw [v5]; rfl
  · simp only [osFold]
    rw [v6, hFe, ← hS]
    simp only [OsSt.quad, polyEval, List.foldr_cons, List.foldr_nil, hagree st.c hb.c,
      hagree st.b hb.b, hagree st.a hb.a]
    ring
  · simp only [OsSt.quad, osFold]
    rw [v10, v6, v7, v8]

/-! ## The rounds -/

/-- A round's next sponge: the squeeze's capacity, the next quadratic's two words waiting. -/
def foldStep (F : Fs) (d0 d2 : E) : Fs := ⟨F.squeeze.2.cap, [(d0, dsObserve), (d2, dsObserve)]⟩

/-- The offset of a round's message in its words. -/
abbrev powOff (b : ℕ) : ℕ := if b = 0 then 0 else 1

/-- A round's nonce in its words. -/
def nonceOf (b : ℕ) (xs : List E) : E := if b = 0 then 0 else xs.getD 0 0

/-- **The honest rounds at `b` bits**: from the sponge `F`, the quadratic `q` and the claim `t`, on
the words `xs` (each round's nonce at `b > 0`, then its two), `n` rounds' sponge, challenges,
quadratic and claim. -/
def foldsTr (b : ℕ) : ℕ → Fs → List E → E → List E → Fs × List E × List E × E
  | 0, F, q, t, _ => (F, [], q, t)
  | n + 1, F, q, _, xs =>
    let G := powSponge b F (nonceOf b xs)
    let c := G.squeeze.1
    let cl := polyEval q c
    let d0 := xs.getD (powOff b) 0
    let d2 := xs.getD (powOff b + 1) 0
    let r := foldsTr b n (foldStep G d0 d2) [d0, cl + d2, d2] cl (xs.drop (roundLen b))
    (r.1, c :: r.2.1, r.2.2.1, r.2.2.2)

/-- Every honest round's proof of work passes. -/
def FoldsPow (b : ℕ) : ℕ → Fs → List E → E → List E → Prop
  | 0, _, _, _, _ => True
  | n + 1, F, q, _, xs =>
    let G := powSponge b F (nonceOf b xs)
    let cl := polyEval q G.squeeze.1
    let d0 := xs.getD (powOff b) 0
    let d2 := xs.getD (powOff b + 1) 0
    PowOk b F (nonceOf b xs) ∧ FoldsPow b n (foldStep G d0 d2) [d0, cl + d2, d2] cl (xs.drop (roundLen b))

theorem foldsTr_chs_length (b : ℕ) : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E),
    (foldsTr b n F q t xs).2.1.length = n
  | 0, _, _, _, _ => rfl
  | n + 1, F, q, t, xs => by simp [foldsTr, foldsTr_chs_length b n]

/-- What the rounds leave. -/
structure FoldsOut (σ : Val) (st st' : OsSt) (r : Fs × List E × List E × E) (m : ℕ) : Prop where
  F : st'.F σ = r.1
  quad : st'.quad σ = r.2.2.1
  t : σ (.n st'.t) = r.2.2.2
  cur : st'.cur σ = st.cur σ * gen ^ m
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ)
  co : st'.co < u128Bound
  below : st'.Below
  pad : st'.pad = st.pad

theorem osFold_below (fr : Option (List String)) (p off : ℕ) (st : OsSt) :
    (osFold fr p off st).2.Below := by
  have := osMat_next st.cb st.co st.k
  refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [osFold] at *
  all_goals omega

theorem osFold_k (fr : Option (List String)) (p off : ℕ) (st : OsSt) : st.k ≤ (osFold fr p off st).2.k := by
  have := osMat_next st.cb st.co st.k
  simp only [osFold]; omega

theorem osFolds_k (fr : Option (List String)) (p : ℕ) :
    ∀ (n off : ℕ) (st : OsSt), st.k ≤ (osFolds fr p off n st).2.k
  | 0, _, _ => le_rfl
  | n + 1, off, st => le_trans (osFold_k fr p off st) (osFolds_k fr p n (off + 1) _)

/-- A state's values agree with an earlier valuation's below its next free value. -/
theorem OsSt.agree {st : OsSt} (hb : st.Below) {σ σ' : Val} (ha : AgreeBelow st.k σ σ') :
    st.fsv σ' = st.fsv σ ∧ st.F σ' = st.F σ ∧ st.quad σ' = st.quad σ ∧
      σ' (.n st.t) = σ (.n st.t) ∧ st.cur σ' = st.cur σ := by
  have hfsv : st.fsv σ' = st.fsv σ := by
    simp only [OsSt.fsv]
    exact List.map_congr_left fun f hf ↦ ha f (hb.fs f hf)
  refine ⟨hfsv, ?_, ?_, ha _ hb.t, ?_⟩
  · simp only [OsSt.F, hfsv, ha _ hb.w0, ha _ hb.w1]
  · simp only [OsSt.quad, ha _ hb.c, ha _ hb.b, ha _ hb.a]
  · simp only [OsSt.cur, ha _ hb.cb]

/-- The capacity of a squeeze is canonical. -/
theorem squeeze_cap_canonical (F : Fs) : AllCanonical F.squeeze.2.cap := capOf_canonical _

/-- The values of `n` rounds from `off`. -/
def foldsF (fr : Option (List String)) (b p : ℕ) : ℕ → ℕ → OsSt → Val → List E → ℕ → E
  | 0, _, _, _, _ => fun _ ↦ 0
  | n + 1, off, st, σ, xs =>
    seqF σ st.k (osFold fr p off st).2.k
      (osFoldF σ st b (nonceOf b xs) (xs.getD (powOff b) 0) (xs.getD (powOff b + 1) 0))
      (fun σ1 ↦ foldsF fr b p n (off + 1) (osFold fr p off st).2 σ1 (xs.drop (roundLen b)))

theorem roundLen_eq (b : ℕ) : roundLen b = powOff b + 2 := by
  unfold roundLen powOff; split_ifs <;> rfl

theorem powWords_split (b : ℕ) (xs : List E) (h : roundLen b ≤ xs.length) :
    (powWords b (nonceOf b xs) ++ [xs.getD (powOff b) 0, xs.getD (powOff b + 1) 0]) =
      xs.take (roundLen b) := by
  unfold powWords nonceOf powOff roundLen at *
  by_cases hb : b = 0
  · simp only [hb, ↓reduceIte] at h ⊢
    match xs, h with
    | a :: b' :: _, _ => rfl
  · simp only [hb, ↓reduceIte] at h ⊢
    match xs, h with
    | a :: b' :: c :: _, _ => rfl

theorem roundLen_zero : roundLen 0 = 2 := rfl

/-- Rounds without a proof of work pass every proof of work. -/
theorem foldsPow_zero : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E), FoldsPow 0 n F q t xs
  | 0, _, _, _, _ => trivial
  | n + 1, _, _, _, _ => ⟨fun h ↦ absurd rfl h, foldsPow_zero n _ _ _ _⟩

/-- **`n` rounds, honestly.** -/
theorem osFolds_complete {fr : Option (List String)} {b : ℕ} {R : E} (hC : FoldCallC C rd fr b R)
    (p : ℕ) : ∀ (n off : ℕ) (st : OsSt) (σ : Val) (xs : List E), σ (.n osRate) = R →
      osRate < st.k → st.fs.length = 5 → st.co < u128Bound →
      st.Below → p < st.k → AllCanonical (st.fsv σ) → xs.length = roundLen b * n →
      ReadsAt rd (st.cur σ) xs → FoldsPow b n (st.F σ) (st.quad σ) (σ (.n st.t)) xs →
      (∀ j, j < n → LoadHolds rd (σ (.n p)) (off + j)
        ((foldsTr b n (st.F σ) (st.quad σ) (σ (.n st.t)) xs).2.1.getD j 0)) →
      BlkF C rd σ st.k (osFolds fr p off n st).2.k (foldsF fr b p n off st σ xs)
        (osFolds fr p off n st).1
        (fun σ' ↦ FoldsOut σ' st (osFolds fr p off n st).2
          (foldsTr b n (st.F σ) (st.quad σ) (σ (.n st.t)) xs) (roundLen b * n) ∧
          AgreeBelow st.k σ σ') := by
  intro n
  induction n with
  | zero =>
    intro off st σ xs _ _ hfs hco hb _ hcan _ _ _ _
    simp only [osFolds]
    refine BlkF.nil fun σ' ha ↦ ⟨?_, ha⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := OsSt.agree hb ha
    exact ⟨e2, e3, e4, by rw [e5]; simp, hfs, by rw [e1]; exact hcan, hco, hb, rfl⟩
  | succ n ih =>
    intro off st σ xs hR hk0 hfs hco hb hp hcan hxl hrd hpw hst
    set nonce := nonceOf b xs
    set d0 := xs.getD (powOff b) 0
    set d2 := xs.getD (powOff b + 1) 0
    set ys := xs.drop (roundLen b)
    have hxl' : roundLen b ≤ xs.length := by rw [hxl, Nat.mul_succ]; omega
    have hsplit := powWords_split b xs hxl'
    have hrd0 : ReadsAt rd (st.cur σ) (powWords b nonce ++ [d0, d2]) := by
      rw [hsplit]
      exact fun k hk ↦ by
        have := hrd k (by simp at hk; omega)
        rwa [List.getElem_take]
    have hrd1 : ReadsAt rd (st.cur σ * gen ^ roundLen b) ys := fun j hj ↦ by
      have := hrd (roundLen b + j) (by simp [ys] at hj; omega)
      rw [loadHolds_mul_gen_pow]
      simpa [ys] using this
    obtain ⟨hpow0, hpw'⟩ := hpw
    have hst0 := hst 0 (by omega)
    simp only [foldsTr, List.getD_cons_zero, Nat.add_zero] at hst0
    have hA := osFold_complete (C := C) hC (p := p) (off := off) σ hR hk0 hfs hco hb hp hcan hrd0
      hpow0 hst0
    set st1 := (osFold fr p off st).2 with hst1
    have hk1 : st.k ≤ st1.k := osFold_k fr p off st
    have hk2 : st1.k ≤ (osFolds fr p (off + 1) n st1).2.k := osFolds_k fr p n (off + 1) st1
    have e : osFolds fr p off (n + 1) st = ((osFold fr p off st).1 ++ (osFolds fr p (off + 1) n st1).1,
        (osFolds fr p (off + 1) n st1).2) := rfl
    rw [e]
    set G := powSponge b (st.F σ) nonce with hG
    set cl := polyEval (st.quad σ) G.squeeze.1 with hcl
    set R' := foldsTr b n (foldStep G d0 d2) [d0, cl + d2, d2] cl ys with hR'
    have hRr : foldsTr b (n + 1) (st.F σ) (st.quad σ) (σ (.n st.t)) xs =
        (R'.1, G.squeeze.1 :: R'.2.1, R'.2.2.1, R'.2.2.2) := rfl
    have hB : ∀ σ1, AgreeBelow st.k σ σ1 → (FoldOutB σ1 st st1 b nonce d0 d2 ∧ AgreeBelow st.k σ σ1) →
        BlkF C rd σ1 st1.k (osFolds fr p (off + 1) n st1).2.k (foldsF fr b p n (off + 1) st1 σ1 ys)
          (osFolds fr p (off + 1) n st1).1
          (fun σ' ↦ FoldsOut σ' st1 (osFolds fr p (off + 1) n st1).2 R' (roundLen b * n) ∧
            st1.cur σ' = st.cur σ * gen ^ roundLen b) := by
      intro σ1 _ ⟨fo, ha1'⟩
      obtain ⟨-, eF, eQ, -, eC⟩ := OsSt.agree hb ha1'
      have eF1 : st1.F σ1 = foldStep G d0 d2 := by rw [fo.sponge, eF]; rfl
      have eq1 : st1.quad σ1 = [d0, cl + d2, d2] := by
        rw [fo.quad, fo.claim, eF, eQ]
      have et1 : σ1 (.n st1.t) = cl := by rw [fo.claim, eF, eQ]
      have ec1 : st1.cur σ1 = st.cur σ * gen ^ roundLen b := by rw [fo.cur, eC]
      have hih := ih (off + 1) st1 σ1 ys (by rw [ha1' _ hk0, hR]) (by simp [st1, osFold])
        fo.fs (by simp [st1, osFold, u128Bound])
        (osFold_below fr p off st) (by omega)
        (by rw [show st1.fsv σ1 = (st1.F σ1).cap from rfl, fo.sponge]
            exact squeeze_cap_canonical _)
        (by simp [ys]; rw [hxl, Nat.mul_succ]; omega)
        (by rw [ec1]; exact hrd1)
        (by rw [eF1, eq1, et1]; exact hpw')
        (fun j hj ↦ by
          have := hst (j + 1) (by omega)
          rw [ha1' p hp, show off + 1 + j = off + (j + 1) by ring, eF1, eq1, et1]
          rw [hRr] at this
          simpa using this)
      rw [eF1, eq1, et1] at hih
      refine BlkF.mono hih fun σ' ⟨ho, ha'⟩ ↦ ⟨ho, ?_⟩
      rw [← ec1]
      exact (OsSt.agree (osFold_below fr p off st) ha').2.2.2.2
    refine BlkF.mono (BlkF.seq hk1 hk2 hA hB) fun σ' ⟨⟨fo, ha'⟩, ho, hc⟩ ↦ ⟨?_, ha'⟩
    rw [hRr]
    exact ⟨ho.F, ho.quad, ho.t, by
      rw [ho.cur, hc, (OsSt.agree hb ha').2.2.2.2, mul_assoc, ← pow_add]; ring_nf, ho.fs, ho.can,
      ho.co, ho.below, by rw [ho.pad]; rfl⟩

end
end LeanVM.Guest.B1.Whir
