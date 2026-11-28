/-
  LeanVM.Guest.B1.VsC.Os.LeftAssembly

  `open_stacked`'s callees at its position, assembled: `OsKidsAt` but its post.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftTail
public import LeanVM.Guest.B1.VsC.Os.LeftQs

/-!
# `open_stacked`'s callees, assembled

`HonRun.osKidsAt_of_post`: at the run's honest data, `OsKidsAt` holds at every position and region,
given only its post on the callees' trees. The window pointers are `osWq` along the chain
`HonRun.osChain` chose from the end of the buffers; at the node's valuation `σ0`, its calls match
`osCallSpec` (`osBody_calls`), split into the levels' (`HonRun.kidsAtF_lvls`) and the tail's
(`HonRun.kidsAtF_tail`), the named callees' meanings from `osCmin_calls`, the region the node's
(`R`, its buffers by `osArm_nodeAt`, the cursor's words and tables), the cells a named callee may
read `osLoadCells`. The callees' posts are `osNodeQs`: the levels' `osLvQs`, then `PostQuiet`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

@[expose] public section

/-- The posts of `open_stacked`'s callees `cl`: the levels', then the tail's quiet. -/
def osNodeQs (c : OsCfg) (os : List (List Opening)) (cl : List Call) : List (Reader → Tree → Prop) :=
  (List.range c.levels.length).flatMap (osLvQs c os) ++
    (cl.drop ((List.range c.levels.length).flatMap (osLvSpec c)).length).map fun _ => PostQuiet

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The sizes `open_stacked`'s end bound reads, every arm: at most `16` levels, each with at most
`2^10` squeezes and queries, a tail of at most `160` callees, buffers of at most `2^30` words. -/
def OsBndOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri =>
    decide ((osCfgR m ri).levels.length ≤ 16) && decide ((osTailSpec (osCfgR m ri)).length ≤ 160) &&
      decide ((osSizesL (osCfgR m ri)).sum ≤ 2 ^ 30) &&
      (List.range (osCfgR m ri).levels.length).all fun l =>
        decide ((osLvA (osCfgR m ri) l).squeezes ≤ 2 ^ 10) && decide ((osLvA (osCfgR m ri) l).queries ≤ 2 ^ 10)

set_option maxRecDepth 100000 in
theorem osBndOk_all : (List.range 15).all OsBndOk = true := by decide +kernel

theorem osBnd {m ri : ℕ} (hm : m < 15) (hri : ri < 4) :
    (osCfgR m ri).levels.length ≤ 16 ∧ (osTailSpec (osCfgR m ri)).length ≤ 160 ∧
      (osSizesL (osCfgR m ri)).sum ≤ 2 ^ 30 ∧ ∀ l < (osCfgR m ri).levels.length,
        (osLvA (osCfgR m ri) l).squeezes ≤ 2 ^ 10 ∧ (osLvA (osCfgR m ri) l).queries ≤ 2 ^ 10 := by
  have h := List.all_eq_true.mp osBndOk_all m (List.mem_range.mpr hm)
  simp only [OsBndOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h ri hri
  exact ⟨a, b, c, d⟩

/-- A chain of cursors each within `K` of the previous one. -/
theorem chain_le {cs : ℕ → ℕ} {K L : ℕ} (h : ∀ l < L, cs (l + 1) ≤ cs l + K) : ∀ l ≤ L, cs l ≤ cs 0 + l * K
  | 0, _ => by simp
  | l + 1, hl => by
    have := chain_le h l (by omega)
    have := h l (by omega)
    rw [Nat.succ_mul]
    omega

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

set_option hygiene false in
local notation "CC" => osCfgR (μ - minOpenLog) (r - 1)

set_option hygiene false in
local notation "HA" => hR.osHonest (cur := ptrAt ic) (tabs := ptrAt it)

set_option hygiene false in
local notation "AR" => rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, ptrAt ic, ptrAt it]

set_option hygiene false in
local notation "ESS" σ0 => (osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0)

set_option linter.constructorNameAsVariable false in
/-- **`OsKidsAt` from its post**, at the run's honest data, every position and region. -/
theorem osKidsAt_of_post (al : String → Bool) (k : ℕ) (hk : 11 ≤ k) (hr1 : 1 ≤ r) (ic it : ℕ) (R : ℕ → Prop)
    (hRx : ∀ i < xs.length, R (ic + i)) (hRt : ∀ n < 2 ^ winTabBits, R (it + n)) (fp c : ℕ)
    (Post : Reader → Tree → Prop)
    (hpost : ∀ (σ0 : Val) (rd0 : Reader),
      OsBodyAt CC c (AR) (ptrAt ic) (ptrAt it) xs w.target w.inner w.residual (HA).own (HA).D rd0 σ0 →
      ∀ (rd : Reader) (σ : Val) (ts : List Tree), LowDef k rd → osPre ic it xs rd →
      OsBodyAt CC c (AR) (ptrAt ic) (ptrAt it) xs w.target w.inner w.residual (HA).own (HA).D rd σ →
      VsC.CallsAgree σ0 σ (calls (ESS σ0)) → Tree.KidsValid coreProgram rd σ (calls (ESS σ0)) ts →
      KidsPost rd (osNodeQs CC os (calls (ESS σ0))) (calls (ESS σ0)) ts →
      Post rd (.node (openName (minOpenLog + (μ - minOpenLog))) σ (allocs σ0 (ESS σ0)) ts)) :
    OsKidsAt B2C.fs al B2C.cert k (μ - minOpenLog) r (AR) ic it xs w.target w.inner w.residual (HA).own (HA).D
      R Post fp c := by
  have hm := hR.m11
  have hr := hR.r4
  obtain ⟨cs, hcs0, hch, hchB⟩ := hR.osChainB (cur := ptrAt ic) (tabs := ptrAt it) al k (by omega) c it R hRt
    (c + (osSizesL CC).sum)
  obtain ⟨hL16, hT160, hsum30, hSQ⟩ := osBnd hm hr
  refine ⟨osWq al CC (fun l => osLpC al CC l (cs l)), osWq_length _ _ _, ?_⟩
  intro σ0 rd0 hl0 hp0 hw0 hb0 _
  have hri : logG (σ0 (.n osRate)) = r - 1 := by
    have h1 := hb0.1 0 (by omega)
    have e : Val.ofArgs (AR) (.n 0) = rateSel r := rfl
    have h0 : σ0 (.n 0) = rateSel r := h1.trans e
    show logG (σ0 (.n 0)) = r - 1
    rw [h0]
    exact logG_rateSel hr1 (by omega)
  have hcm := osBody_calls hm hr hri
  rw [osCallSpec_eq] at hcm
  obtain ⟨cl1, cl2, hcl, f1, f2⟩ := forall₂_append_split _ _ hcm
  have hcall := osCmin_calls hm hb0 hri
  have hv := hb0.2.2.1.2.2.2
  have hal0 := (osArm_nodeAt hm B2C.cert fp (openName (minOpenLog + (μ - minOpenLog))) hb0.2.2.1).1
  have hmem0 := osWords_mem hw0
  have h0 : OsNF CC c (HA).own (ptrAt ic) (ptrAt it) xs rd0 := ⟨hp0.1, hp0.2, hmem0⟩
  have hS0 : OsNF CC c (HA).own (ptrAt ic) (ptrAt it) xs (restrict rd0 (osLoadCells CC c ic it xs)) :=
    ⟨readsAt_restrict' hp0.1 fun k hk => Or.inl ⟨k, hk, rfl⟩,
      winTabs_restrict hp0.2 fun n hn => Or.inr (Or.inl ⟨n, hn, rfl⟩),
      fun j hj hne => readsAt_restrict' (hmem0 j hj hne) fun k hk => by
        have hl' : (osOwnA (HA).own j).length = (osSizesL CC).getD j 0 := forall₂_getD (HA).own_len j
        exact Or.inr (Or.inr ⟨j, hj, by omega, by omega⟩)⟩
  have hRb : ∀ i, osBufCells CC c i → R i ∨ ownData B2C.cert fp c (openName (minOpenLog + (μ - minOpenLog)))
      (allocs σ0 (ESS σ0)) (ESS σ0) i := fun i ⟨q, hq, h1, h2⟩ => Or.inr (Or.inl ⟨q, by rw [hal0]; exact hq, h1, h2⟩)
  have hRS : ∀ i, osLoadCells CC c ic it xs i → R i ∨ ownData B2C.cert fp c (openName (minOpenLog + (μ - minOpenLog)))
      (allocs σ0 (ESS σ0)) (ESS σ0) i := by
    rintro i (⟨j, hj, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨j, hj, h1, h2⟩)
    · exact Or.inl (hRx j hj)
    · exact Or.inl (hRt n hn)
    · exact hRb _ ⟨_, mem_zip_bases hj, h1, h2⟩
  have hL := hR.kidsAtF_lvls (cur := ptrAt ic) (tabs := ptrAt it) al k σ0 rd0 c it rfl R
    (fun i => R i ∨ ownData B2C.cert fp c (openName (minOpenLog + (μ - minOpenLog))) (allocs σ0 (ESS σ0)) (ESS σ0) i)
    (osLoadCells CC c ic it xs) (osPre ic it xs) (fun i h => Or.inl h) hRb hRS (fun _ h => h) cs hch
    (fun rd => HoldsWords rd (osWords CC c (HA).own (osWq al CC fun l => osLpC al CC l (cs l)))) (fun _ => False)
    (fun _ h => h) hv h0 hS0 _ le_rfl f1 (fun c' hc' => hcall c' (by rw [hcl]; exact List.mem_append_left _ hc'))
  obtain ⟨e, heT, hT⟩ := hR.kidsAtF_tailB (cur := ptrAt ic) (tabs := ptrAt it) al k σ0 rd0 c
    (fun i => R i ∨ ownData B2C.cert fp c (openName (minOpenLog + (μ - minOpenLog))) (allocs σ0 (ESS σ0)) (ESS σ0) i)
    (osLoadCells CC c ic it xs) (osPre ic it xs) hRb hRS (fun _ h => h)
    (fun rd => HoldsWords rd (osWords CC c (HA).own (osWq al CC fun l => osLpC al CC l (cs l)))) (fun _ => False)
    (fun _ h => osWords_mem h) hv h0 hS0 f2 (fun c' hc' => hcall c' (by rw [hcl]; exact List.mem_append_right _ hc'))
    (cs (CC).levels.length) (fun l hl => (hSQ l (by have := hR.yr; omega)).2)
  have hKF := kidsAtF_append _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [osLvsQs_length]; exact f1.length_eq.symm) hL hT
  have hq : osNodeQs CC os (calls (ESS σ0)) =
      (List.range (CC).levels.length).flatMap (osLvQs CC os) ++ cl2.map fun _ => PostQuiet := by
    rw [osNodeQs, hcl, List.drop_left' f1.length_eq]
  refine ⟨e, osNodeQs CC os (calls (ESS σ0)),
    fun rd => HoldsWords rd (osWords CC c (HA).own (osWq al CC fun l => osLpC al CC l (cs l))), fun _ => False,
    fun hF => ?_, ?_, fun _ h => h, ?_⟩
  · have hK : ∀ l < (CC).levels.length, cs (l + 1) ≤ cs l + 2054 * (3 * 2 ^ 16 + 2048) := fun l hl =>
      le_trans (hchB _ hF l hl) (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have := hSQ l hl; omega)) _)
    have hcL := chain_le hK _ le_rfl
    have h1 := heT hF
    have h2 := Nat.mul_le_mul_right (2054 * (3 * 2 ^ 16 + 2048)) hL16
    have h3 : cl2.length * 2 ^ 28 ≤ 160 * 2 ^ 28 := Nat.mul_le_mul_right _ (by rw [f2.length_eq]; exact hT160)
    have := p16; have := p28
    have : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    have : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
    omega
  · rw [hq, hal0, ← hcs0, hcl]
    rw [hal0] at hKF
    with_reducible exact hKF
  · intro rd σ ts hl hp _ hb hag hkv hkp
    with_reducible exact hpost σ0 rd0 hb0 rd σ ts hl hp hb hag hkv hkp

end
end LeanVM.Guest.B1.Whir.HonRun

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

@[expose] public section

/-- **What is left of `open_stacked`: its post.** At every accepting run's honest data, the recorded
queries split level by level, every node valuation and callees' trees the callees' posts
`osNodeQs` hold of: the node pops the run's Merkle hints stream by stream and every node is exact. -/
def OsPostHyp (k : ℕ) : Prop :=
  ∀ (μ r : ℕ) (target : E) (S : KeccakState) (root : Digest) (xs : List E) (os : List (List Opening))
    (w : WhirEnd) (cfg : List Whir.Level) (Ls : List LvAt) (hR : HonRun μ r target S root xs os w cfg Ls)
    (qs : List (ℕ × List ℕ)),
    Prover.merkleHints true qs os =
      (List.range (osCfgR (μ - minOpenLog) (r - 1)).levels.length).flatMap (fun l =>
        Hints.levelHints (l == 0) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth (os.getD l []).length
          (os.getD l [])) →
    ∀ (ic it c : ℕ) (σ0 : Val) (rd0 : Reader),
      OsBodyAt (osCfgR (μ - minOpenLog) (r - 1)) c
        (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, ptrAt ic, ptrAt it])
        (ptrAt ic) (ptrAt it) xs w.target w.inner w.residual
        (hR.osHonest (cur := ptrAt ic) (tabs := ptrAt it)).own (hR.osHonest (cur := ptrAt ic) (tabs := ptrAt it)).D
        rd0 σ0 →
      ∀ (rd : Reader) (σ : Val) (ts : List Tree), LowDef k rd → osPre ic it xs rd →
      OsBodyAt (osCfgR (μ - minOpenLog) (r - 1)) c
        (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, ptrAt ic, ptrAt it])
        (ptrAt ic) (ptrAt it) xs w.target w.inner w.residual
        (hR.osHonest (cur := ptrAt ic) (tabs := ptrAt it)).own (hR.osHonest (cur := ptrAt ic) (tabs := ptrAt it)).D
        rd σ →
      VsC.CallsAgree σ0 σ (calls ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0))) →
      Tree.KidsValid coreProgram rd σ (calls ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0))) ts →
      KidsPost rd (osNodeQs (osCfgR (μ - minOpenLog) (r - 1)) os
          (calls ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0))))
        (calls ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0))) ts →
      SameStreams ((Memory.Tree.node (openName (minOpenLog + (μ - minOpenLog))) σ
          (allocs σ0 ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0))) ts).pops coreProgram rd)
          (Prover.merkleHints true qs os) ∧
        (Memory.Tree.node (openName (minOpenLog + (μ - minOpenLog))) σ
          (allocs σ0 ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).flatMap (fdEvs σ0))) ts).Every
          (ExactAt coreProgram rd)

/-- **`OsKidsHyp` from `open_stacked`'s post.** -/
theorem osKidsHyp_of_post {al : String → Bool} {k : ℕ} (hk : 11 ≤ k) (hP : OsPostHyp k) :
    OsKidsHyp B2C.fs al B2C.cert k := by
  intro m hm r root fsv target ic it xs os w s' roots' qs R hr1 hr4 _ hcar hrun hq hRx hRt fp c _
  obtain ⟨hosl, -, hmh⟩ := merkleHints_open hm hr1 hr4 hcar hrun hq
  obtain ⟨S, cfg, Ls, rfl, hR⟩ := osHonRun_of_open hm hr1 hr4 hcar hrun hq
  have h := hR.osKidsAt_of_post al k hk hr1 ic it R hRx hRt fp c
    (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧ t.Every (ExactAt coreProgram rd))
    (hP _ r target S root xs os w cfg Ls hR qs hmh ic it c)
  have key : ∃ H : OsHonestA (osCfgR (minOpenLog + m - minOpenLog) (r - 1))
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, ofK (addressOfIndex ic),
        ofK (addressOfIndex it)])
      (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs w.target w.inner w.residual
      (w.point ++ List.replicate (pointCap - (minOpenLog + m)) 0)
      (w.point.map (1 + ·) ++ List.replicate (pointCap - (minOpenLog + m)) 1),
      OsKidsAt B2C.fs al B2C.cert k (minOpenLog + m - minOpenLog) r
        (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, ofK (addressOfIndex ic),
          ofK (addressOfIndex it)])
        ic it xs w.target w.inner w.residual H.own H.D R
        (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧
          t.Every (ExactAt coreProgram rd)) fp c := ⟨_, h⟩
  rw [Nat.add_sub_cancel_left] at key
  exact key

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.VsC

@[expose] public section

/-- **`open_stacked` completes placed at every arm** from its post. -/
theorem openStackedCompleteA_of_post {al : String → Bool} {k : ℕ} (hk : 11 ≤ k) (hP : OsPostHyp k) :
    ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs al B2C.cert k m :=
  openStackedCompleteA_of_kids hk (osKidsHyp_of_post hk hP)

end
end LeanVM.Guest.B1.VsC
