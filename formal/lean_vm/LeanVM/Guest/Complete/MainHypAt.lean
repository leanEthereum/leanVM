/-
  LeanVM.Guest.Complete.MainHypAt

  `main`'s window at its honest oracle: the choice of oracle, memory and words made, what is left.
-/

module

public import LeanVM.Guest.Complete.MainOrc
public import LeanVM.Guest.Complete.MainWinCall
import LeanVM.Guest.B1.Main.Plan
import LeanVM.Guest.Complete.CoverageEq

/-!
# `main`'s windows at the honest oracle

`MainWinHyp al k s w` asks for an evaluation memory, an oracle and `main`'s own words. They are chosen:
`mRd0 s w cover` (the memory holding `main`'s words and the header), `mOrc al s w` (the honest oracle) and
`mainWords s w cover`; `MainHypAt al k s w cover` is `MainHyp` there, the `HeapBuf`s `MainCounts.bufs`
(`mAllocs`), and `mainWinHyp_of_at` gives `MainWinHyp` from it on the claims' cells `ClaimCells`.
`MainHypFromCallees al k`: `MainHypAt` from `MainCalleesAt` on every node; `mainWinHypFromCallees_of_at`.

Facts for the windows: the coverage count `slots_eq_cov` (the slots are the raw signatures and the
children's claims, `kidBase_all`), `count_def` (a count at most the slots has its word defined on the
memories the windows see, at `17 ≤ k`), and the call windows keeping the cursor
(`winsHypT_call_of_atEvery'`, `winsHypT_cif_of_atEvery'`: the rest from an end past the callee's block).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The coverage count -/

/-- **The slots are the coverage count**: the raw signatures and the children's claims. -/
theorem slots_eq_cov {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w) :
    (mainCounts s w).sx + (mainCounts s w).ss = coverageSlots w := by
  have h1 := B1.Main.planSlots_eq (s := s) (w := w) hr.1
  have h2 := B1.Main.coverage_eq s w
  have ex : (xPlan s w).duplicates = (B1.Main.xPlan s w).duplicates := (coveragePlan_eq _ _ _).1
  have es : (sPlan s w).duplicates = (B1.Main.sPlan s w).duplicates := (coveragePlan_eq _ _ _).1
  have ex' : (mainCounts s w).nxd = (B1.Main.xPlan s w).duplicates.length := congrArg List.length ex
  have es' : (mainCounts s w).nsd = (B1.Main.sPlan s w).duplicates.length := congrArg List.length es
  simp only [List.length_append] at h2
  have e1 : (mainCounts s w).nlx = s.claims.xmss.length := rfl
  have e2 : (mainCounts s w).nls = s.claims.sphincs.length := rfl
  show (mainCounts s w).nlx + (mainCounts s w).nxd + ((mainCounts s w).nls + (mainCounts s w).nsd) = coverageSlots w
  omega

/-- The write count after every child is the coverage count. -/
theorem kidBase_all (w : NodeWitness) : kidBase w w.children.length = coverageSlots w := by
  simp [kidBase, coverageSlots, List.take_length]

/-- The raw signatures are at most the slots. -/
theorem raw_le_slots {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w) :
    (mainCounts s w).nrx + (mainCounts s w).nrs ≤ (mainCounts s w).sx + (mainCounts s w).ss := by
  rw [slots_eq_cov hr]
  show w.xmssSignatures.length + w.sphincsSignatures.length ≤ coverageSlots w
  unfold coverageSlots
  omega

/-! ## A count's word -/

/-- **A count at most the slots has its word defined** on a memory defined below `2^k` (`17 ≤ k`)
and holding `main`'s words: below `main`'s frame's end by `LowDef`, else in `main`'s buffers. -/
theorem count_def {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader} {k c : ℕ} (hk : 17 ≤ k)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hc : c ≤ (mainCounts s w).sx + (mainCounts s w).ss) (hL : LowDef k rd)
    (hW : HoldsWords rd (mainWords s w cover)) : (rd (addressOfIndex c)).isSome := by
  by_cases h : c < B2C.fs "main"
  · have h17 : (2 : ℕ) ^ 17 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact hL c (lt_of_lt_of_le (lt_trans h fs_main_lt) h17)
  · refine isSome_of_inW hW (mainWords_cover hl (by omega) ?_)
    have hc' : c ≤ (mainCounts s w).nlx + (mainCounts s w).nxd + ((mainCounts s w).nls + (mainCounts s w).nsd) := hc
    simp only [mTop, MainCounts.bufs, MainCounts.sx, MainCounts.ss, List.sum_cons, List.sum_nil]
    omega

/-! ## Calls keeping the cursor -/

variable {al : String → Bool} {k : ℕ} {σ0 : Val} {w : ℕ → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **A call window from its callee's `AtEvery`**, the rest from an end past its block. -/
theorem winsHypT_call_of_atEvery' {s : Stmt} {g : String} {ws : List W1} {st : St} {K : St → Prop}
    {args rets : List E} {Rg : ℕ → Prop} {Preg : Reader → Prop} {Post : Reader → Tree → Prop} {B lo Tc β : ℕ}
    (he : Enters σ0 g s) (ha : (argsOf s).map σ0 = args) (hr : (retsOf s).map σ0 = rets)
    (h : AtEveryB al k g args rets Rg Preg Post B lo Tc β) (hTc : 2 ^ 58 ≤ Tc)
    (hβ : B + β ≤ 2 ^ 51) (hlo : lo ≤ allocBase (al g) st.kc)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : ∀ ec, allocBase (al g) st.kc + B ≤ ec → WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre (.call s :: ws) st K := by
  obtain ⟨e, hb, hc⟩ := h (allocBase (al g) st.kc) (allocBase (al g) st.kc + B) hlo le_rfl
  have hce : allocBase (al g) st.kc + B ≤ e := by obtain ⟨_, _, h, _⟩ := hc; exact h
  rw [WinsHypT]
  refine ⟨g, Post, B, e, Rg, fun _ => False, fun _ => True, he, hR, ?_, end_step hTc hβ hb, hrest e hce⟩
  rw [ha, hr]
  exact hc.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)

/-- **A guarded call window from its callee's `AtEvery`**, the rest from an end past its block when
taken. -/
theorem winsHypT_cif_of_atEvery' {c : V} {g : String} {as : List V} {ws : List W1} {st : St} {K : St → Prop}
    {n : ℕ} {args : List E} {Rg : ℕ → Prop} {Preg : Reader → Prop} {Post : Reader → Tree → Prop} {B lo Tc β : ℕ}
    (hn : n < 2 ^ 34) (hc : σ0 c = word 1 0 + gen ^ n) (ha : as.map σ0 = args)
    (htk : coreProgram.Takes g args.length = true)
    (h : n ≠ 0 → AtEveryB al k g args [] Rg Preg Post B lo Tc β)
    (hTc : 2 ^ 58 ≤ Tc) (hβ : B + β ≤ 2 ^ 51) (hlo : lo ≤ allocBase (al g) st.kc)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hT : n ≠ 0 → ∀ ec, allocBase (al g) st.kc + B ≤ ec → WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K)
    (hZ : n = 0 → WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, allocBase (al g) st.kc + B2C.fs (tailKey g), st.O, st.D, st.Qs ++ [fun _ _ => True]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre (.cif c g as :: ws) st K := by
  rw [WinsHypT]
  refine ⟨by rw [hc, word_one]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n),
    fun h0 => ?_, fun h0 => ?_⟩
  · have hn0 : n ≠ 0 := fun e => h0 (by rw [hc]; exact (guard_eq_zero_iff hn).mpr e)
    obtain ⟨e, hb, hcl⟩ := h hn0 (allocBase (al g) st.kc) (allocBase (al g) st.kc + B) hlo le_rfl
    have hce : allocBase (al g) st.kc + B ≤ e := by obtain ⟨_, _, h, _⟩ := hcl; exact h
    refine ⟨Post, B, e, Rg, fun _ => False, fun _ => True, hR, ?_, end_step hTc hβ hb, hT hn0 e hce⟩
    rw [ha]
    exact hcl.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)
  · have hn0 : n = 0 := (guard_eq_zero_iff hn).mp (by rw [← hc]; exact h0)
    refine ⟨?_, lt_trans (B2C.fs_lt _) (by norm_num), hZ hn0⟩
    rw [ha]
    exact phantom_of_takes htk

/-! ## The choice made -/

/-- **The claims' cells** `main`'s buffers hold: `55` per child's fresh claim, `26` per child's deferred
claim and the node's own. -/
structure ClaimCells (s : NodeStatement) (w : NodeWitness) : Prop where
  fresh : ∀ ch ∈ w.children, ch.freshClaim.cells.length = 55
  carried : ∀ ch ∈ w.children, ch.statement.deferredClaim.cells.length = 26
  own : s.deferredClaim.cells.length = 26

/-- **`main`'s windows' hypotheses at its honest oracle**, memory and words, its `HeapBuf`s
`MainCounts.bufs`. -/
def MainHypAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  MainHyp B2C.fs al B2C.cert k (mRd0 s w cover) (mOrc al s w)
    (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
    (· < 2) (mainPreR s)
    ⟨B2C.fs "main", mTop (mainCounts s w), fun rd => HoldsWords rd (mainWords s w cover), fun _ => False, []⟩
    fun st => ∀ rd, LowDef k rd → mainPreR s rd → st.O rd → ∀ ts,
      Tree.KidsValid coreProgram rd (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd)
        (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
      KidsPost rd st.Qs (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
      mainPostR s w rd (.node "main" (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd) (mainCounts s w).bufs ts)

/-- **`MainWinHyp` from the windows' hypotheses at the honest oracle.** -/
theorem mainWinHyp_of_at {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) (hn : (mainCounts s w).nc ≤ 16)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) (h : MainHypAt al k s w cover) :
    MainWinHyp al k s w := by
  have ha := mAllocs (al := al) (rd := mRd0 s w cover) hb hn
  refine ⟨mRd0 s w cover, mOrc al s w, mainWords s w cover, ?_, mCalls_le _, ?_, ?_⟩
  · rw [ha]
    simp only [MainCounts.bufs, List.sum_cons, List.sum_nil]
    omega
  · rw [ha]
    obtain ⟨hin, hd⟩ := mainWords_in hl
    unfold WordsInA
    exact ⟨fun q hq => Or.inr (hin q hq), hd⟩
  · simp only [mSt0]
    rw [ha]
    exact h

/-- **What is left of `main`'s window**: its windows' hypotheses at the honest oracle, on every node
and every coverage table the callees' fields hold on. -/
def MainHypFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → ∀ cover : List E,
        cover.length = (mainCounts s w).sx + (mainCounts s w).ss → MainCalleesAt al k s w cover →
        MainHypAt al k s w cover

/-- **`MainWinHypFromCallees` from the windows at the honest oracle** and the claims' cells. -/
theorem mainWinHypFromCallees_of_at {al : String → Bool} {k : ℕ}
    (hcc : ∀ s w, NodeRelation guestBytecode guestSeed s w → ChildrenOk guestBytecode guestSeed w →
      ClaimCells s w)
    (h : MainHypFromCallees al k) : MainWinHypFromCallees al k := by
  intro hk hk' hc hvs s w hr hl hok
  obtain ⟨cover, hlen, hat⟩ := hc.callees s w hr hl hok
  have cc := hcc s w hr hok
  exact mainWinHyp_of_at (slots_lt hr hl) (nc_le hl) (mainLists_length hlen cc.fresh cc.carried cc.own)
    (h hk hk' hc hvs s w hr hl hok cover hlen hat)

end
end LeanVM.Guest.Complete
