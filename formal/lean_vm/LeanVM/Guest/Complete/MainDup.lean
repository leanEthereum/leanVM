module

public import LeanVM.Guest.Complete.DupA
public import LeanVM.Guest.Complete.Limits
public import LeanVM.Guest.B1.Main.Plan
import LeanVM.Guest.Binding
import LeanVM.Guest.Complete.CoverageEq
import LeanVM.Facts.ClaimBytes
import LeanVM.Guest.Memory.Uniform

/-!
# The duplicate claims' loops at `main`'s honest arguments

`dup_atEvery`: a duplicates' loop over the claims `U` after the declared `D`, their cells (`4` each)
read from `T` on every memory `Pre` admits and lying in `R`, completes placed from its first
iteration at every frame and cursor past its block (`dupL_callAtA` at `j = 0`), its pops the
duplicates' cells in order. `mainDupx`, `mainDups`: `MainCalleesAt`'s fields `dupx`, `dups`, given the
duplicates below `2^34`, which `NodeRelation` and the memory budget give (`nxd_lt`, `nsd_lt`: the
coverage table below `2^19` slots).

`MainCalleesOpenAt`: `MainCalleesAt` without the fields proved here; `MainCalleesOpenA.toMainCalleesA`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The `j`-th claim's cells, none past the list. -/
def dupCells {α : Type} (f : α → List E) (l : List α) (j : ℕ) : List E :=
  if h : j < l.length then f l[j] else []

theorem dupPops_eq {α : Type} (f : α → List E) (l : List α) :
    dupPops (dupCells f l) 0 l.length = l.map fun c => ("dup_claims", f c) := by
  apply List.ext_getElem (by simp [dupPops])
  intro i h1 h2
  have hi : i < l.length := by simpa using h2
  simp [dupPops, dupCells, hi]

theorem readsAt_slot {α : Type} {rd : Reader} {T : ℕ} {f : α → List E} {D U : List α}
    (hf : ∀ c, (f c).length = 4) (h : ReadsAt rd (ptrAt T) ((D ++ U).flatMap f)) {j : ℕ}
    (hj : j < U.length) : ReadsAt rd (ptrAt (T + 4 * (D.length + j))) (dupCells f U j) := by
  have := B1.Main.readsAt_flatMap_of (D ++ U) (fun a _ => hf a) h (D.length + j) (by simp; omega)
  rw [ptrAt_mul_gen_pow] at this
  have e : (D ++ U)[D.length + j]'(by simp; omega) = U[j] := by
    rw [List.getElem_append_right (by omega)]; simp
  rw [e] at this
  simpa [dupCells, hj] using this

/-- **A duplicates' loop completes placed from its first iteration** at every frame and cursor
past its block. -/
theorem dup_atEvery {α : Type} {al : String → Bool} {k : ℕ} {L : String} {fn : Fn} {f : α → List E}
    {D U : List α} {T lo Tc β : ℕ} {R : ℕ → Prop} {Pre : Reader → Prop}
    (hst : coreProgram.find? L = some fn ∧ fn.body = dupPre L ++ [.ret []] ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ coreProgram.loop L = true ∧
      Stmt.blockNextOk isComputed pinsInverse fn.body = true)
    (hn : U.length < 2 ^ 34) (hf : ∀ c, (f c).length = 4)
    (hR : ∀ i, T ≤ i → i < T + 4 * (D.length + U.length) → R i)
    (hP : ∀ rd, Pre rd → ReadsAt rd (ptrAt T) ((D ++ U).flatMap f)) (hne : U.length ≠ 0) :
    AtEveryB al k L [1, gen ^ U.length, ptrAt T, gen ^ D.length] [] R Pre
      (PopsPost (U.map fun c => ("dup_claims", f c))) (loopBlock L U.length) lo Tc β := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hst
  have hlen : ∀ j < U.length, (dupCells f U j).length = 4 := fun j hj => by
    simp [dupCells, hj, hf]
  have hreg : ∀ j < U.length, ∀ i < 4, R (T + 4 * (D.length + j) + i) := fun j hj i hi =>
    hR _ (by omega) (by omega)
  have hpre : ∀ rd, Pre rd → ∀ j < U.length, ReadsAt rd (ptrAt (T + 4 * (D.length + j))) (dupCells f U j) :=
    fun rd hp j hj => readsAt_slot hf (hP rd hp) hj
  have H : DupHyps L fn U.length T D.length (dupCells f U) R Pre := ⟨h1, h2, h3, h4, h5, hn, hlen, hreg, hpre⟩
  refine atEveryB_of_le fun fp cur _ hfc => ?_
  obtain ⟨e, hle, he⟩ := dupL_callAtA (al := al) (k := k) H 0 (Nat.pos_of_ne_zero hne) fp cur
    (by simpa using hfc)
  refine ⟨e, hle, ?_⟩
  rw [dupPops_eq] at he
  simpa [dupArgs] using he

/-! ## `main`'s two loops -/

theorem xCells_length (c : LeanXmssClaim) : (xCells c).length = 4 := by
  have h : (claimBytes xmssPublicKeyBytes c).length = 64 := by
    rw [claimBytes_xmss]; exact Binding.length_claimBytes _ _ _
  simp only [xCells, Prover.cellsOfBytes, List.length_map, List.length_range, h]

theorem sCells_length (c : LeanSphincsClaim) : (sCells c).length = 4 := by
  have h : (claimBytes Sphincs.PublicKey.toBytes c).length = 64 := by
    rw [claimBytes_sphincs]; exact Binding.length_claimBytes _ _ _
  simp only [sCells, Prover.cellsOfBytes, List.length_map, List.length_range, h]

theorem mBase_zero (m : MainCounts) : mBase m 0 = B2C.fs "main" := by
  simp [mBase, MainCounts.bufs, bases]

theorem mBase_one (m : MainCounts) : mBase m 1 = B2C.fs "main" + 4 * m.sx := by
  simp [mBase, MainCounts.bufs, bases]

theorem mTop_ge (m : MainCounts) : B2C.fs "main" + 4 * m.sx + 4 * m.ss ≤ mTop m := by
  simp only [mTop, MainCounts.bufs, List.sum_cons, List.sum_nil]; omega

theorem mainWords_x {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (h : MainPreA al s w cover rd) :
    ReadsAt rd (ptrAt (mBase (mainCounts s w) 0)) ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap xCells) :=
  h.1 (mBase (mainCounts s w) 0, (s.claims.xmss ++ (xPlan s w).duplicates).flatMap xCells)
    (by simp only [mainWords]; exact List.mem_cons_self)

theorem mainWords_s {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (h : MainPreA al s w cover rd) :
    ReadsAt rd (ptrAt (mBase (mainCounts s w) 1))
      ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap sCells) :=
  h.1 (mBase (mainCounts s w) 1, (s.claims.sphincs ++ (sPlan s w).duplicates).flatMap sCells)
    (by simp only [mainWords]; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- **`dupx`**: the leanXMSS duplicates' loop at `main`'s honest arguments. -/
theorem mainDupx {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hn : (mainCounts s w).nxd < 2 ^ 34) : (mainCounts s w).nxd ≠ 0 → AtEveryB al k "__loop0_main"
      [1, gen ^ (mainCounts s w).nxd, mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx] []
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost ((xPlan s w).duplicates.map fun c => ("dup_claims", xCells c)))
      (loopBlock "__loop0_main" (mainCounts s w).nxd) (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) := by
  rw [show mPtr (mainCounts s w) 0 0 = ptrAt (mBase (mainCounts s w) 0) from by simp [mPtr]]
  exact dup_atEvery (D := s.claims.xmss) (U := (xPlan s w).duplicates) (T := mBase (mainCounts s w) 0)
      dupHyps0_static hn xCells_length
      (fun i h1 h2 => Or.inl (by
        have := mTop_ge (mainCounts s w)
        rw [mBase_zero] at h1 h2
        exact ⟨by omega, by simp only [MainCounts.sx, mainCounts] at this h2 ⊢; omega⟩))
      (fun _ hp => mainWords_x hp)

/-- **`dups`**: the leanSPHINCS duplicates' loop at `main`'s honest arguments. -/
theorem mainDups {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hn : (mainCounts s w).nsd < 2 ^ 34) : (mainCounts s w).nsd ≠ 0 → AtEveryB al k "__loop1_main"
      [1, gen ^ (mainCounts s w).nsd, mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls] []
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost ((sPlan s w).duplicates.map fun c => ("dup_claims", sCells c)))
      (loopBlock "__loop1_main" (mainCounts s w).nsd) (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) := by
  rw [show mPtr (mainCounts s w) 1 0 = ptrAt (mBase (mainCounts s w) 1) from by simp [mPtr]]
  exact dup_atEvery (D := s.claims.sphincs) (U := (sPlan s w).duplicates) (T := mBase (mainCounts s w) 1)
      dupHyps1_static hn sCells_length
      (fun i h1 h2 => Or.inl (by
        have := mTop_ge (mainCounts s w)
        rw [mBase_one] at h1 h2
        exact ⟨by omega, by simp only [MainCounts.sx, MainCounts.ss, mainCounts] at this h2 ⊢; omega⟩))
      (fun _ hp => mainWords_s hp)

/-- **The duplicates are below `2^19`** on a node with `NodeRelation` within the memory budget. -/
theorem dups_lt {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w)
    (hl : DeployedLimits s w) : (mainCounts s w).nxd < 2 ^ 19 ∧ (mainCounts s w).nsd < 2 ^ 19 := by
  have h1 := B1.Main.planSlots_eq (s := s) (w := w) hr.1
  have h2 := B1.Main.coverage_eq s w
  have h3 := coverageSlots_lt_of_budget hl.withinMemoryBudget
  have ex : (xPlan s w).duplicates = (B1.Main.xPlan s w).duplicates := (coveragePlan_eq _ _ _).1
  have es : (sPlan s w).duplicates = (B1.Main.sPlan s w).duplicates := (coveragePlan_eq _ _ _).1
  have ex' : (mainCounts s w).nxd = (B1.Main.xPlan s w).duplicates.length := congrArg List.length ex
  have es' : (mainCounts s w).nsd = (B1.Main.sPlan s w).duplicates.length := congrArg List.length es
  simp only [List.length_append] at h2
  exact ⟨by omega, by omega⟩

/-! ## The callees left -/

/-- **`main`'s callees left**: `MainCalleesAt` without `dupx`, `dups`. -/
structure MainCalleesOpenAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) :
    Prop where
  clx : AtEveryB al k "claim_list_digest" [mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx]
    (Prover.digestCells (claimListDigest xmssPublicKeyBytes s.claims.xmss)) (mainR al (mainCounts s w))
    (MainPreA al s w cover) (PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells)))
    (B2C.fs "claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  csp : AtEveryB al k "claim_list_digest" [mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls]
    (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs))
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells)))
    (B2C.fs "claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  rawx : (mainCounts s w).nrx ≠ 0 → AtEveryB al k "__loop2_main"
    ([1, gen ^ (mainCounts s w).nrx, gen ^ (mainCounts s w).sx, mPtr (mainCounts s w) 2 0,
      mPtr (mainCounts s w) 0 0] ++ Main.lxTagWords) []
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap fun cs =>
      ("raw_index", [Prover.count cs.2]) :: Prover.xmssHints cs.1.1.1 cs.1.1.2 cs.1.2))
    (loopBlock "__loop2_main" (mainCounts s w).nrx) (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  raws : (mainCounts s w).nrs ≠ 0 → AtEveryB al k "__loop3_main"
    [1, gen ^ (mainCounts s w).nrs, gen ^ (mainCounts s w).ss, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
      gen ^ (mainCounts s w).nrx, mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 3 0] []
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap fun cs =>
      ("sp_raw_index", [Prover.count cs.2]) :: Prover.sphincsHints cs.1.1.1 cs.1.1.2 cs.1.2))
    (loopBlock "__loop3_main" (mainCounts s w).nrs) (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  da : ∀ c mw, w.daMatrix = some (c, mw) → AtEveryB al k "da_verify" [mPtr (mainCounts s w) 3 0]
    (Prover.digestCells c.daRoot ++ [c.membershipChallenge]) (mainR al (mainCounts s w))
    (MainPreA al s w cover) (PopsPost (Prover.daHints c mw)) (B2C.fs "da_verify") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  kidx : ∀ c (hc : c < w.children.length), AtEveryB al k "child_claim_list_digest"
    [mPtr (mainCounts s w) 0 0, mPtr (mainCounts s w) 2 0, gen ^ kidBase w c, gen ^ (mainCounts s w).sx,
      gen ^ w.children[c].statement.claims.xmss.length]
    (Prover.digestCells (claimListDigest xmssPublicKeyBytes w.children[c].statement.claims.xmss))
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost (Prover.childSlotPushes ((xPlan s w).childSlots.getD c [])))
    (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  kids : ∀ c (hc : c < w.children.length), AtEveryB al k "child_claim_list_digest"
    [mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
      gen ^ kidBase w c * gen ^ w.children[c].statement.claims.xmss.length, gen ^ (mainCounts s w).ss,
      gen ^ w.children[c].statement.claims.sphincs.length]
    (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes w.children[c].statement.claims.sphincs))
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost (Prover.childSlotPushes ((sPlan s w).childSlots.getD c [])))
    (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  agg : w.children ≠ [] → AtEveryB al k "aggregate_claims"
    [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
      mPtr (mainCounts s w) 9 0, ptrAt (mGS al (mainCounts s w) + winTabAt)] []
    (mainR al (mainCounts s w)) (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
    (B2C.fs "aggregate_claims") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)

/-- **`main`'s callees left, on every node.** -/
structure MainCalleesOpenA (al : String → Bool) (k : ℕ) : Prop where
  callees : ∀ (s : NodeStatement) (w : NodeWitness), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → ∃ cover : List E,
      cover.length = (mainCounts s w).sx + (mainCounts s w).ss ∧ MainCalleesOpenAt al k s w cover

/-- **`MainCalleesAt` from the callees left**, the duplicates below `2^34`. -/
theorem MainCalleesOpenAt.toAt {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness}
    {cover : List E} (h : MainCalleesOpenAt al k s w cover) (hx : (mainCounts s w).nxd < 2 ^ 34)
    (hs : (mainCounts s w).nsd < 2 ^ 34) : MainCalleesAt al k s w cover :=
  ⟨h.clx, h.csp, mainDupx hx, mainDups hs, h.rawx, h.raws, h.da, h.kidx, h.kids, h.agg⟩

/-- **`MainCalleesA` from the callees left.** -/
theorem MainCalleesOpenA.toMainCalleesA {al : String → Bool} {k : ℕ} (h : MainCalleesOpenA al k) :
    MainCalleesA al k :=
  ⟨fun s w hr hl hok => by
    obtain ⟨cover, hc, ho⟩ := h.callees s w hr hl hok
    obtain ⟨hx, hs⟩ := dups_lt hr hl
    exact ⟨cover, hc, ho.toAt (hx.trans (by norm_num)) (hs.trans (by norm_num))⟩⟩

end
end LeanVM.Guest.Complete
