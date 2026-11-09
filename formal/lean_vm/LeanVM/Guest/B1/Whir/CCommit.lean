/-
  LeanVM.Guest.B1.Whir.CCommit

  A level's next commitment and its proof of work, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinal
public import LeanVM.Guest.B1.Whir.Commit
public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The next commitment, honestly

`osCommit_complete`: the root's two halves (a digest's), the out-of-domain value and intro and
the nonce at the cursor, the root's halves in `level_roots`, the out-of-domain point
(`commitS1`'s challenge, then the squeezes) at its slot of `ood_z`, the value and intro in `ood`,
the nonce's proof of work passing: the block, with `grind_check` after it, holds, the
permutation after the nonce (`commitS2`) carried (`CommitOutC`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- Cell `c` of a state, `0` past the thirteen. -/
def cells13F (S : KeccakState) (c : ℕ) : E := if h : c < 13 then cellsOfState S false ⟨c, h⟩ else 0

/-- The sponge before the out-of-domain point: the two waiting scalars and the root's halves. -/
def commitF1 (σ : Val) (st : OsSt) (ra rb : E) : Fs :=
  ⟨st.fsv σ, [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve), (ra, dsObserve),
    (rb, dsObserve)]⟩

/-- The squeezes after the out-of-domain point's first coordinate. -/
def commitRest (σ : Val) (st : OsSt) (ra rb : E) (m : ℕ) : List E × Fs :=
  (⟨capOf (commitF1 σ st ra rb).perm, []⟩ : Fs).squeezeN (m - 1)

/-- The sponge the nonce's permutation reads. -/
def commitF2 (σ : Val) (st : OsSt) (ra rb : E) (m : ℕ) (y c0 c2 nonce : E) : Fs :=
  ⟨(commitRest σ st ra rb m).2.cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve),
    (nonce, dsPowNonce)]⟩

/-- The block's values, by segments from its first value. -/
def commitSegs (plan : List (ℕ × ℕ × ℕ)) (σ : Val) (st : OsSt) (lvl m : ℕ) (ra rb y c0 c2 nonce : E) :
    List (ℕ × (ℕ → E)) :=
  [(5, fun i ↦ (st.fsv σ).getD i 0), (9, fsPackVals (σ (.n st.w0)) 1),
    (9, fsPackVals (σ (.n st.w1)) 1), (1, fun _ ↦ ra), (9, fsPackVals ra 1), (1, fun _ ↦ rb),
    (9, fsPackVals rb 1), (2, fun _ ↦ 0),
    (1, fun _ ↦ gw (osMatSD plan st.mats osOodz ((lvl + 1) * ligColsCap)).2),
    (1, fun _ ↦ σ (.n osOodz) * gw ((lvl + 1) * ligColsCap)),
    (5, fun i ↦ (commitRest σ st ra rb m).2.cap.getD i 0), (1, fun _ ↦ y), (9, fsPackVals y 1),
    (1, fun _ ↦ c0), (9, fsPackVals c0 1), (1, fun _ ↦ c2), (9, fsPackVals c2 1),
    (1, fun _ ↦ nonce), (5, fun i ↦ (commitRest σ st ra rb m).2.cap.getD i 0),
    (9, fsPackVals nonce 4), (13, cells13F (commitF2 σ st ra rb m y c0 c2 nonce).perm)]

/-- What a next commitment leaves: the nonce's permutation's capacity carried, nothing waiting. -/
structure CommitOutC (σ : Val) (st st' : OsSt) (S : KeccakState) : Prop where
  fsv : st'.fsv σ = capOf S
  cur : st'.cur σ = st.cur σ * gen ^ 6
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ)
  co : st'.co = st.co + 6
  below : st'.Below
  pad : st'.pad = st.pad
  w0 : st'.w0 = st.w0
  w1 : st'.w1 = st.w1
  mats : MatsOk σ st'.mats
  matsB : MatsBelow st'.k st'.mats

theorem capOf_canonical (S : KeccakState) : AllCanonical (capOf S) := by
  intro c hc
  simp only [capOf, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _

theorem pendCells_canonical (pend : List (E × ℕ)) : AllCanonical (pendCells pend) := by
  intro c hc
  simp only [pendCells, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hc
  obtain ⟨p, -, hp | hp⟩ := hc
  · rw [hp]; exact (scalarCells_canonical _ _).1
  · rw [hp]; exact (scalarCells_canonical _ _).2

theorem squeezeN_cap_canonical : ∀ (n : ℕ) (F : Fs), AllCanonical F.cap →
    AllCanonical (F.squeezeN n).2.cap
  | 0, _, h => h
  | n + 1, _, _ => squeezeN_cap_canonical n _ (capOf_canonical _)

theorem osCommit_below (plan : List (ℕ × ℕ × ℕ)) (lvl : ℕ) (lv : OsLv) {st : OsSt} (hb : st.Below) :
    (osCommit plan lvl lv st).2.1.Below := by
  have := hb.w0; have := hb.w1; have := hb.c; have := hb.b; have := hb.a; have := hb.t
  have := hb.cb
  refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [osCommit] at *
  all_goals omega

/-- **The next commitment and its proof of work, honestly.** -/
theorem osCommit_complete {plan : List (ℕ × ℕ × ℕ)}
    (hCan : ∀ args rets, MeaningAssertCanonical args rets → C "assert_canonical" args rets)
    {lvl : ℕ} {lv : OsLv}
    (hOod : ∀ args rets, MeaningOpeningOodPoint lv.logCols rd args rets →
      C ("opening_ood_point__L" ++ natStr lv.logCols) args rets)
    (hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
      C ("grind_check__L" ++ natStr lv.grind) args rets)
    {st : OsSt} (σ : Val) (hfs : st.fs.length = 5) (hb : st.Below) (hk : 164 ≤ st.k)
    (hcan : AllCanonical (st.fsv σ)) (hlvl : (lvl + 1) * ligColsCap < u128Bound)
    (hm : MatsOk σ st.mats) (hmb : MatsBelow st.k st.mats)
    {ra rb y c0 c2 nonce : E} {d : Digest} (hd : (ra, rb) = digestHalves d)
    (hrd : ReadsAt rd (st.cur σ) [ra, rb, y, c0, c2, nonce])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) ra)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) rb)
    (hz : ReadsAt rd (σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap))
      (challengeOf (commitF1 σ st ra rb).perm :: (commitRest σ st ra rb lv.logCols).1))
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2)
    (hpow : powOk Whir.queryGrindingBits nonce
      (commitF2 σ st ra rb lv.logCols y c0 c2 nonce).squeeze.1 = true) :
    BlkF C rd σ st.k (osCommit plan lvl lv st).2.1.k
      (fun j ↦ segLookup (commitSegs plan σ st lvl lv.logCols ra rb y c0 c2 nonce) (j - st.k))
      ((osCommit plan lvl lv st).1 ++
        [.call ("grind_check__L" ++ natStr lv.grind) [.n (osCommit plan lvl lv st).2.2] []])
      (fun σ' ↦ CommitOutC σ' st (osCommit plan lvl lv st).2.1
        (commitF2 σ st ra rb lv.logCols y c0 c2 nonce).perm ∧ AgreeBelow st.k σ σ') := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  set segs := commitSegs plan σ st lvl lv.logCols ra rb y c0 c2 nonce with hsegs
  have hlen : segLen segs = 110 := by simp [hsegs, commitSegs, segLen]
  intro σ' ha hv
  have HV : ∀ j < segLen segs, σ' (.n (st.k + j)) = segLookup segs j := fun j hj ↦ by
    rw [hv _ (by omega) (by simp only [osCommit]; omega)]
    show segLookup segs (st.k + j - st.k) = _
    rw [Nat.add_sub_cancel_left]
  have sv := seg_val HV
  have hagree : ∀ i < st.k, σ' (.n i) = σ (.n i) := ha
  have hfl : ∀ f ∈ st.fs, f < st.k := hb.fs
  rw [hf] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  obtain ⟨efsv, -, -, -, eC⟩ := OsSt.agree hb ha
  set k := st.k with hkdef
  -- the segments' values
  have seg : ∀ (m : ℕ) (hm : m < segs.length) (o : ℕ), segLen (segs.take m) = o → ∀ i,
      i < segs[m].1 → σ' (.n (k + o + i)) = segs[m].2 i := sv
  have one : ∀ (m : ℕ) (hm : m < segs.length) (o : ℕ), segLen (segs.take m) = o →
      0 < segs[m].1 → σ' (.n (k + o)) = segs[m].2 0 := fun m hm o ho h0 ↦ by
    have := seg m hm o ho 0 h0; rwa [Nat.add_zero] at this
  have pk : ∀ (m o : ℕ) (hm : m < segs.length), segLen (segs.take m) = o → segs[m].1 = 9 →
      ∀ x t, segs[m].2 = fsPackVals x t → ∀ i < 9, σ' (.n (k + o + i)) = fsPackVals x t i := by
    intro m o hm ho h9 x t hx i hi
    rw [seg m hm o ho i (by omega), hx]
  have L : segs.length = 21 := by simp [hsegs, commitSegs]
  -- the cursor's words
  have hcur : ∀ j (hj : j < 6), LoadHolds rd (σ' (.n st.cb)) (st.co + j)
      ([ra, rb, y, c0, c2, nonce][j]) := fun j hj ↦ by
    rw [hagree _ hb.cb, ← loadHolds_mul_gen_pow]
    exact hrd j (by simpa using hj)
  -- the values used
  have vra : σ' (.n (k + 23)) = ra := one 3 (by omega) 23 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs])
  have vrb : σ' (.n (k + 33)) = rb := one 5 (by omega) 33 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs])
  have vy : σ' (.n (k + 52)) = y := one 11 (by omega) 52 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs])
  have vc0 : σ' (.n (k + 62)) = c0 := one 13 (by omega) 62 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs])
  have vc2 : σ' (.n (k + 72)) = c2 := one 15 (by omega) 72 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs])
  have vn : σ' (.n (k + 82)) = nonce := one 17 (by omega) 82
    (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
  have va : ∀ i < 2, σ' (.n (k + 43 + i)) = 0 := fun i hi ↦
    seg 7 (by omega) 43 (by simp [hsegs, segLen, commitSegs]) i (by simp [hsegs, commitSegs]; omega)
  have v45 : σ' (.n (k + 45)) = gw (osMatSD plan st.mats osOodz ((lvl + 1) * ligColsCap)).2 :=
    one 8 (by omega) 45
    (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
  have v46 : σ' (.n (k + 46)) = σ (.n osOodz) * gw ((lvl + 1) * ligColsCap) := one 9 (by omega) 46
    (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
  have vcap : ∀ i < 5, σ' (.n (k + 47 + i)) = (commitRest σ st ra rb lv.logCols).2.cap.getD i 0 :=
    fun i hi ↦ seg 10 (by omega) 47 (by simp [hsegs, segLen, commitSegs]) i
      (by simp [hsegs, commitSegs]; omega)
  have vcap2 : ∀ i < 5, σ' (.n (k + 83 + i)) = (commitRest σ st ra rb lv.logCols).2.cap.getD i 0 :=
    fun i hi ↦ seg 18 (by omega) 83 (by simp [hsegs, segLen, commitSegs]) i
      (by simp [hsegs, commitSegs]; omega)
  have vout : ∀ i < 13, σ' (.n (k + 97 + i)) =
      cells13F (commitF2 σ st ra rb lv.logCols y c0 c2 nonce).perm i :=
    fun i hi ↦ seg 20 (by omega) 97 (by simp [hsegs, segLen, commitSegs]) i
      (by simp [hsegs, commitSegs]; omega)
  have hS1 : (commitF1 σ st ra rb).perm = permOf ([σ' (.n (k + 11)), σ' (.n (k + 13)),
      σ' (.n (k + 20)), σ' (.n (k + 22)), σ' (.n (k + 30)), σ' (.n (k + 32)), σ' (.n (k + 40)),
      σ' (.n (k + 42))] ++ st.fsv σ) := by
    have e11 := pk 1 5 (by omega) (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
      (σ (.n st.w0)) 1 (by simp [hsegs, commitSegs]) 6 (by omega)
    have e13 := pk 1 5 (by omega) (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
      (σ (.n st.w0)) 1 (by simp [hsegs, commitSegs]) 8 (by omega)
    have e20 := pk 2 14 (by omega) (by simp [hsegs, segLen, commitSegs])
      (by simp [hsegs, commitSegs]) (σ (.n st.w1)) 1 (by simp [hsegs, commitSegs]) 6 (by omega)
    have e22 := pk 2 14 (by omega) (by simp [hsegs, segLen, commitSegs])
      (by simp [hsegs, commitSegs]) (σ (.n st.w1)) 1 (by simp [hsegs, commitSegs]) 8 (by omega)
    have e30 := pk 4 24 (by omega) (by simp [hsegs, segLen, commitSegs])
      (by simp [hsegs, commitSegs]) ra 1 (by simp [hsegs, commitSegs]) 6 (by omega)
    have e32 := pk 4 24 (by omega) (by simp [hsegs, segLen, commitSegs])
      (by simp [hsegs, commitSegs]) ra 1 (by simp [hsegs, commitSegs]) 8 (by omega)
    have e40 := pk 6 34 (by omega) (by simp [hsegs, segLen, commitSegs])
      (by simp [hsegs, commitSegs]) rb 1 (by simp [hsegs, commitSegs]) 6 (by omega)
    have e42 := pk 6 34 (by omega) (by simp [hsegs, segLen, commitSegs])
      (by simp [hsegs, commitSegs]) rb 1 (by simp [hsegs, commitSegs]) 8 (by omega)
    have c1 := fsPackVals_cells (σ (.n st.w0)) 1
    have c2' := fsPackVals_cells (σ (.n st.w1)) 1
    have c3 := fsPackVals_cells ra 1
    have c4 := fsPackVals_cells rb 1
    simp only [Prod.ext_iff] at c1 c2' c3 c4
    rw [commitF1, perm_eq_cells _ (by simp)]
    simp only [Nat.add_assoc, Nat.reduceAdd] at e11 e13 e20 e22 e30 e32 e40 e42
    rw [e11, e13, e20, e22, e30, e32, e40, e42, c1.1, c1.2, c2'.1, c2'.2, c3.1, c3.2, c4.1, c4.2]
    simp [pendCells, dsObserve]
  have hfsv : st.fsv σ = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [OsSt.fsv, hf]
  have a0 := hagree f0 hfl.1; have a1 := hagree f1 hfl.2.1; have a2 := hagree f2 hfl.2.2.1
  have a3 := hagree f3 hfl.2.2.2.1; have a4 := hagree f4 hfl.2.2.2.2
  have aw0 := hagree _ hb.w0; have aw1 := hagree _ hb.w1
  have hrt : σ' (.n osRoots) = σ (.n osRoots) := hagree _ (by unfold osRoots; omega)
  have hoz : σ' (.n osOodz) = σ (.n osOodz) := hagree _ (by unfold osOodz; omega)
  have hoo : σ' (.n osOod) = σ (.n osOod) := hagree _ (by unfold osOod; omega)
  have hcanr : IsCanonical128 ra ∧ IsCanonical128 rb := by
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hd
    simp only at h1 h2
    rw [h1, h2]
    exact ⟨(isCanonical128_ofLimbs_iff _ _ _).mpr rfl, (isCanonical128_ofLimbs_iff _ _ _).mpr rfl⟩
  set F2 := commitF2 σ st ra rb lv.logCols y c0 c2 nonce with hF2
  set cap2 := (commitRest σ st ra rb lv.logCols).2.cap with hcap2
  have hcl : cap2.length = 5 := by
    rw [hcap2, commitRest]
    have := squeezeN_cap_length (lv.logCols - 1) (⟨capOf (commitF1 σ st ra rb).perm, []⟩ : Fs)
      (by simp [capOf])
    exact this
  obtain ⟨q0, q1, q2, q3, q4, hq⟩ : ∃ q0 q1 q2 q3 q4, cap2 = [q0, q1, q2, q3, q4] := by
    match h : cap2, hcl with
    | [q0, q1, q2, q3, q4], _ => exact ⟨q0, q1, q2, q3, q4, rfl⟩
  have hcan2 : AllCanonical cap2 := squeezeN_cap_canonical _ _ (capOf_canonical _)
  rw [hq] at vcap vcap2 hcan2
  -- the pack facts
  have fp : ∀ (m o : ℕ) (hm : m < segs.length) (x : Core.V) (t : ℕ),
      segLen (segs.take m) = o → segs[m].1 = 9 → segs[m].2 = fsPackVals (σ' x) t →
      FsPackOk σ' x (k + o) t := fun m o hm x t ho h9 hx ↦
    fsPackOk_of_vals fun i hi ↦ pk m o hm ho h9 (σ' x) t hx i hi
  have SL : ∀ m, segLen (segs.take m) = segLen ((commitSegs plan σ st lvl lv.logCols ra rb y c0 c2
      nonce).take m) := fun _ ↦ rfl
  have pc : ∀ (m o : ℕ) (hm : m < segs.length) (x : E) (t : ℕ), segLen (segs.take m) = o →
      segs[m].1 = 9 → segs[m].2 = fsPackVals x t →
      σ' (.n (k + o + 6)) = (Keccak.scalarCells x t).1 ∧
        σ' (.n (k + o + 8)) = (Keccak.scalarCells x t).2 := fun m o hm x t ho h9 hx ↦ by
    have c := fsPackVals_cells x t
    simp only [Prod.ext_iff] at c
    rw [pk m o hm ho h9 x t hx 6 (by omega), pk m o hm ho h9 x t hx 8 (by omega), c.1, c.2]
    exact ⟨rfl, rfl⟩
  have pw0 := pc 1 5 (by omega) (σ (.n st.w0)) 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have pw1 := pc 2 14 (by omega) (σ (.n st.w1)) 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have pra := pc 4 24 (by omega) ra 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have prb := pc 6 34 (by omega) rb 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have py := pc 12 53 (by omega) y 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have pc0 := pc 14 63 (by omega) c0 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have pc2 := pc 16 73 (by omega) c2 1 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  have pn := pc 19 88 (by omega) nonce 4 (by simp [hsegs, segLen, commitSegs])
    (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs])
  simp only [Nat.add_assoc, Nat.reduceAdd] at pw0 pw1 pra prb py pc0 pc2 pn
  have sc := fun x t ↦ scalarCells_canonical x t
  -- the new capacity
  have hfsv' : (osCommit plan lvl lv st).2.1.fsv σ' = capOf F2.perm := by
    have o8 := vout 8 (by omega); have o9 := vout 9 (by omega); have o10 := vout 10 (by omega)
    have o11 := vout 11 (by omega); have o12 := vout 12 (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at o8 o9 o10 o11 o12
    simp only [OsSt.fsv, osCommit, List.map_cons, List.map_nil]
    rw [o8, o9, o10, o11, o12]
    simp [cells13F, capOf]
  refine ⟨?_, ⟨hfsv', ?_, by simp [osCommit], by rw [hfsv']; exact capOf_canonical _, rfl,
    osCommit_below plan lvl lv hb, rfl, rfl, rfl, ?_, ?_⟩, ha⟩
  have hoff0 : (lvl + 1) * ligColsCap ≠ 0 := by unfold ligColsCap; omega
  have hsd := osMatSD_ok (plan := plan) hm (base := osOodz) hlvl
  have hsrc : σ' (.n (osMatSD plan st.mats osOodz ((lvl + 1) * ligColsCap)).1) =
      σ (.n (osMatSD plan st.mats osOodz ((lvl + 1) * ligColsCap)).1) :=
    hagree _ (osMatSD_lt hmb (by unfold osOodz; omega))
  · simp only [osCommit, allOk_append]
    rw [← hkdef, osMatP_eq _ hoff0]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- the capacity copied
      rw [hf]
      simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons,
        allOk_nil, and_true, StmtOk, Atom.Holds, Nat.zero_add, Nat.add_zero]
      have c : ∀ i < 5, σ' (.n (k + i)) = (st.fsv σ).getD i 0 := fun i hi ↦ by
        have := seg 0 (by omega) 0 (by simp [hsegs, segLen]) i (by simp [hsegs, commitSegs]; omega)
        simpa [hsegs, commitSegs] using this
      rw [hfsv] at c
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := c 0 (by omega); simp at this; rw [this, a0]
      · have := c 1 (by omega); simp at this; rw [this, a1]
      · have := c 2 (by omega); simp at this; rw [this, a2]
      · have := c 3 (by omega); simp at this; rw [this, a3]
      · have := c 4 (by omega); simp at this; rw [this, a4]
    · exact (allOk_fsPackT _ _ _).mpr (fp 1 5 (by omega) (.n st.w0) 1
        (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
        (by simp [hsegs, commitSegs, aw0]))
    · exact (allOk_fsPackT _ _ _).mpr (fp 2 14 (by omega) (.n st.w1) 1
        (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
        (by simp [hsegs, commitSegs, aw1]))
    · refine (allOk_fsNextT _ _ _).mpr ⟨by rw [vra]; exact hcur 0 (by omega), ?_⟩
      exact fp 4 24 (by omega) (.n (k + 23)) dsObserve (by simp [hsegs, segLen, commitSegs])
        (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs, vra, dsObserve])
    · refine (allOk_fsNextT _ _ _).mpr ⟨by rw [vrb]; exact hcur 1 (by omega), ?_⟩
      exact fp 6 34 (by omega) (.n (k + 33)) dsObserve (by simp [hsegs, segLen, commitSegs])
        (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs, vrb, dsObserve])
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil]
      have a43 := va 0 (by omega); have a44 := va 1 (by omega)
      rw [Nat.add_zero] at a43
      exact ⟨hCan _ _ ⟨by rw [vra]; exact hcanr.1, by rw [a43]⟩,
        hCan _ _ ⟨by rw [vrb]; exact hcanr.2, by rw [a44]⟩, by rw [vra, hrt]; exact hr0,
        by rw [vrb, hrt]; exact hr1⟩
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨v45, by rw [v46, v45, hsrc, gw_eq hsd.1, hsd.2, gw_eq hlvl]⟩
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil, osRun,
        List.range_succ, List.range_zero, hf, Nat.add_zero, List.cons_append, List.nil_append]
      refine hOod _ _ ?_
      have cq : ∀ i < 5, σ' (.n (k + 47 + i)) = [q0, q1, q2, q3, q4].getD i 0 := vcap
      have q0' := cq 0 (by omega); have q1' := cq 1 (by omega); have q2' := cq 2 (by omega)
      have q3' := cq 3 (by omega); have q4' := cq 4 (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, List.getD_cons_zero,
        List.getD_cons_succ] at q0' q1' q2' q3' q4'
      rw [a0, a1, a2, a3, a4, pw0.1, pw0.2, pw1.1, pw1.2, pra.1, pra.2, prb.1, prb.2, v46,
        q0', q1', q2', q3', q4']
      have e1 : [(Keccak.scalarCells (σ (.n st.w0)) 1).1, (Keccak.scalarCells (σ (.n st.w0)) 1).2,
          (Keccak.scalarCells (σ (.n st.w1)) 1).1, (Keccak.scalarCells (σ (.n st.w1)) 1).2,
          (Keccak.scalarCells ra 1).1, (Keccak.scalarCells ra 1).2, (Keccak.scalarCells rb 1).1,
          (Keccak.scalarCells rb 1).2, σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] =
          pendCells (commitF1 σ st ra rb).pend ++ List.replicate 0 0 ++ (commitF1 σ st ra rb).cap := by
        simp [pendCells, commitF1, hfsv, dsObserve]
      have hS : permOf [(Keccak.scalarCells (σ (.n st.w0)) 1).1,
          (Keccak.scalarCells (σ (.n st.w0)) 1).2,
          (Keccak.scalarCells (σ (.n st.w1)) 1).1, (Keccak.scalarCells (σ (.n st.w1)) 1).2,
          (Keccak.scalarCells ra 1).1, (Keccak.scalarCells ra 1).2, (Keccak.scalarCells rb 1).1,
          (Keccak.scalarCells rb 1).2, σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] =
          (commitF1 σ st ra rb).perm := by
        rw [e1]
        exact (perm_eq_cells _ (by simp [commitF1])).symm
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rw [hfsv] at hcan
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact (sc _ _).1 | exact (sc _ _).2
          | exact hcan _ (by simp)
      · show ReadsAt rd (σ (.n osOodz) * gw ((lvl + 1) * ligColsCap)) _
        rw [hS, gw_eq hlvl]
        exact hz
      · show [q0, q1, q2, q3, q4] = _
        rw [hS, ← hq]
        rfl
    · refine (allOk_fsNextT _ _ _).mpr ⟨by rw [vy]; exact hcur 2 (by omega), ?_⟩
      exact fp 12 53 (by omega) (.n (k + 52)) dsObserve (by simp [hsegs, segLen, commitSegs])
        (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs, vy, dsObserve])
    · refine (allOk_fsNextT _ _ _).mpr ⟨by rw [vc0]; exact hcur 3 (by omega), ?_⟩
      exact fp 14 63 (by omega) (.n (k + 62)) dsObserve (by simp [hsegs, segLen, commitSegs])
        (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs, vc0, dsObserve])
    · refine (allOk_fsNextT _ _ _).mpr ⟨by rw [vc2]; exact hcur 4 (by omega), ?_⟩
      exact fp 16 73 (by omega) (.n (k + 72)) dsObserve (by simp [hsegs, segLen, commitSegs])
        (by simp [hsegs, commitSegs]) (by simp [hsegs, commitSegs, vc2, dsObserve])
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨by rw [vy, hoo]; exact hy, by rw [vc0, hoo]; exact hc0, by rw [vc2, hoo]; exact hc2,
        by rw [vn]; exact hcur 5 (by omega)⟩
    · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [vcap2 0 (by omega), vcap 0 (by omega)]
      · rw [vcap2 1 (by omega), vcap 1 (by omega)]
      · rw [vcap2 2 (by omega), vcap 2 (by omega)]
      · rw [vcap2 3 (by omega), vcap 3 (by omega)]
      · rw [vcap2 4 (by omega), vcap 4 (by omega)]
    · exact (allOk_fsPackT _ _ _).mpr (fp 19 88 (by omega) (.n (k + 82)) 4
        (by simp [hsegs, segLen, commitSegs]) (by simp [hsegs, commitSegs])
        (by simp [hsegs, commitSegs, vn]))
    · simp only [allOk_cons, allOk_nil, and_true]
      have cq : ∀ i < 5, σ' (.n (k + 83 + i)) = [q0, q1, q2, q3, q4].getD i 0 := vcap2
      have q0' := cq 0 (by omega); have q1' := cq 1 (by omega); have q2' := cq 2 (by omega)
      have q3' := cq 3 (by omega); have q4' := cq 4 (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, List.getD_cons_zero,
        List.getD_cons_succ] at q0' q1' q2' q3' q4'
      have hins : ([k + 59, k + 61, k + 69, k + 71, k + 79, k + 81, k + 94, k + 96, k + 83, k + 84,
          k + 85, k + 86, k + 87].map V.n).map σ' =
          pendCells F2.pend ++ List.replicate 0 0 ++ F2.cap := by
        simp only [List.map_cons, List.map_nil]
        rw [py.1, py.2, pc0.1, pc0.2, pc2.1, pc2.2, pn.1, pn.2, q0', q1', q2', q3', q4']
        simp [pendCells, hF2, commitF2, ← hcap2, hq, dsObserve, dsPowNonce]
      show (Atom.keccak _ _ false false).Holds rd σ'
      apply keccakA_of (rd := rd) (by rfl) (by rfl)
      · rw [hins]
        intro x hx
        simp only [List.mem_append, List.mem_replicate] at hx
        rcases hx with (hx | hx) | hx
        · exact pendCells_canonical _ x hx
        · omega
        · rw [hF2, commitF2, ← hcap2] at hx
          exact hcan2 _ (by rw [← hq]; exact hx)
      · rw [hins, show permOf (pendCells F2.pend ++ List.replicate 0 0 ++ F2.cap) = F2.perm from
          (perm_eq_cells _ (by simp [hF2, commitF2])).symm]
        funext c
        simp only [cells13, osRun, List.map_map, Function.comp_def]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.isLt,
          Option.map_some, Option.getD_some]
        have := vout c.val c.isLt
        simp only [cells13F, c.isLt, ↓reduceDIte] at this
        exact this
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil]
      apply hGr
      have := vout 0 (by omega)
      rw [Nat.add_zero] at this
      rw [this]
      exact grind_meaning (by decide) hpow
  · simp only [OsSt.cur, osCommit, pow_add, mul_assoc]
  · have hoff0 : (lvl + 1) * ligColsCap ≠ 0 := by unfold ligColsCap; omega
    have hm' : MatsOk σ' st.mats := matsOk_agree hm hmb hagree
    show MatsOk σ' (osMatsAfter plan st.mats osOodz ((lvl + 1) * ligColsCap) (k + 45))
    unfold osMatsAfter
    simp only [hoff0, ↓reduceIte]
    split
    · exact hm'
    · intro m hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hm' m hmem
      · simp only [List.mem_singleton] at hmem
        subst hmem
        obtain ⟨hd, hs⟩ := osMatSrc_ok (plan := plan) hm' (base := osOodz) hlvl
        refine ⟨hlvl, hd, ?_, hs⟩
        show σ' (.n (k + 46)) = σ' (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap)
        rw [v46, hoz, gw_eq hlvl]
  · show MatsBelow (k + 110) (osMatsAfter plan st.mats osOodz ((lvl + 1) * ligColsCap) (k + 45))
    exact matsBelow_after hmb (by unfold osOodz; omega) (by omega) (by omega)

end
end LeanVM.Guest.B1.Whir
