module

public import LeanVM.Guest.Complete.DaVerifyA
public import LeanVM.Guest.Complete.DaVerify
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# `da_verify`, placed

`da_verify(bb)` at frame `fp` and cursor `c`: its roots buffer (`128` words, the tree over the blob
roots, `rootsCells`) its own words at `c`; its callees from `c + 128`: `da_padding`, the dual
codeword's builders (`DaVectorCompleteA`, `DaWeightsCompleteA`, open: their words at positions their
placement chooses, claimed as their data, held by every memory holding their words), the blob loop
(`dvL_callAtA`), `da_pad` (`da_pad_callAtA`) and the roots' levels (`dl_callAtA`). It loads the
count word at `bb·g^r` only (`dv_callAtA`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

set_option linter.constructorNameAsVariable false

/-- The cells of `da_vector`'s returned words (`vecWords`). -/
def vecR (bz bt bc bo : ℕ) (i : ℕ) : Prop :=
  (bz ≤ i ∧ i < bz + 14) ∨ (bt ≤ i ∧ i < bt + 256) ∨ (bc ≤ i ∧ i < bc + 128) ∨ (bo ≤ i ∧ i < bo + 896)

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **`da_vector` completes placed** at every frame and cursor past its frame: its returned words
at positions its placement chooses, claimed as its data, held by every memory holding its words. -/
def DaVectorCompleteA (k : ℕ) : Prop :=
  ∀ (z : E) (fp c : ℕ), fp + fs "da_vector" ≤ c → ∃ (bz bt bc bo e : ℕ), e ≤ c + 2 ^ 30 ∧
    CallAtA fs al cert k "da_vector" [z] (vecRets bz bt bc bo) (fun _ => False) (vecR bz bt bc bo)
      (fun rd => HoldsWords rd (vecWords z bz bt bc bo)) (fun _ => True) FreePost (fs "da_vector") fp c e

/-- **`da_weights` completes placed** at every frame and cursor past its frame, on `da_vector`'s
words, loading them: the weights table and the columns' runs at positions its placement chooses,
claimed as its data. -/
def DaWeightsCompleteA (k : ℕ) : Prop :=
  ∀ (z : E) (bz bt bc bo fp c : ℕ), fp + fs "da_weights" ≤ c → ∃ (bw : ℕ) (bcol : ℕ → ℕ) (e : ℕ),
    e ≤ c + 2 ^ 30 ∧ CallAtA fs al cert k "da_weights" [gen ^ (bt + 128), gen ^ bc, gen ^ bz, gen ^ bo] [gen ^ bw]
      (vecR bz bt bc bo) (wsR bw bcol) (fun rd => HoldsWords rd (wsWords z bw bcol))
      (fun rd => HoldsWords rd (vecWords z bz bt bc bo)) FreePost (fs "da_weights") fp c e

variable {fs al cert}

theorem dv_not_loop : coreProgram.loop "da_verify" = false := by decide +kernel

set_option linter.unusedTactic false in
set_option maxRecDepth 100000 in
/-- **`da_verify` completes placed** on a witness opening `(root, z)`, given its dual codeword's
builders placed: at frame `fp` and cursor `c`, on the count table at index `qb`, loading only its
count word in `R`. -/
theorem dv_callAtA (hfs : ∀ g, fs g < 2 ^ 16) (hwf : coreProgram.Wf) {k : ℕ} (hk : 16 ≤ k)
    (hV : DaVectorCompleteA fs al cert k)
    (hWs : DaWeightsCompleteA fs al cert k) {w : LeanVM.Da.MatrixWitness} {root : Digest} {z : E}
    (hw : w.Opens root z) {qb : ℕ} {R : ℕ → Prop} (hR : ∀ j ≤ LeanDa.maxRows, R (qb + j)) {fp c : ℕ}
    (hfc : fp + fs "da_verify" ≤ c) :
    ∃ e, e ≤ c + 2 ^ 38 ∧ CallAtA fs al cert k "da_verify" [ptrAt qb] (digestCells root ++ [z]) R (fun _ => False) (fun _ => True)
      (fun rd => CountWords rd (ptrAt qb))
      (fun rd t => t.pops coreProgram rd = dvPops' z w.rows.length (wSyms w) ∧ t.Every (ExactAt coreProgram rd))
      (fs "da_verify") fp c e := by
  set r := w.rows.length with hrdef
  set syms := wSyms w with hsyms
  have hr1 : 1 ≤ r := hw.1
  have hr : r ≤ LeanDa.maxRows := hw.2.1
  have hr32 : r ≤ 32 := hr
  have hsl : ∀ i h, (syms i h).length = LeanDa.cellSymbols := wSyms_len hw
  have horth : ∀ i < r, runSum z (syms i) 128 = 0 := by
    intro i hi
    have := wDot hw i hi
    rw [← this, runSum, list_sum_range]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [cellDot, show LeanDa.cellSymbols = 128 from rfl, list_sum_range]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_range.mp he
    rw [colWs, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have hroot : root = daRoot r 5 syms := opens_eq hw
  have hmr : LeanDa.maxRows = 32 := rfl
  -- the callees, from `c + 128`
  set Ld := name% «da_verify_loop0»
  set Bp := fs "da_padding" with hBp
  set e1 := allocBase (al "da_padding") (c + 128) + Bp with he1
  have hP := da_padding_callAtA (fs := fs) (al := al) (cert := cert) hwf hk hr1 hr (fun _ => False)
    (allocBase (al "da_padding") (c + 128)) e1
  obtain ⟨bz, bt, bc, bo, e2, he2, hVv⟩ := hV z (allocBase (al "da_vector") e1)
    (allocBase (al "da_vector") e1 + fs "da_vector") le_rfl
  obtain ⟨bw, bcol, e3, he3, hWw⟩ := hWs z bz bt bc bo (allocBase (al "da_weights") e2)
    (allocBase (al "da_weights") e2 + fs "da_weights") le_rfl
  obtain ⟨e4, he4, hL⟩ := dvL_callAtA (fs := fs) (al := al) (cert := cert) hfs k z (r := r) (by omega) hsl horth
    (bw := bw)
    (bcol := bcol) (qR := c) 0 (by omega) (allocBase (al Ld) e3) (allocBase (al Ld) e3 + lpBlk fs Ld (r - 0)) le_rfl
  have hPd := da_pad_callAtA (fs := fs) (al := al) (cert := cert) k (q := c) (r := r) (d := LeanDa.maxRows - r)
    (by omega) (fp := allocBase (al "da_pad") e4) (c := allocBase (al "da_pad") e4 + fs "da_pad") le_rfl
  set e5 := allocBase (al name% «da_pad_loop0») (allocBase (al "da_pad") e4 + fs "da_pad") +
    padBlock fs (LeanDa.maxRows - r)
  obtain ⟨e6, he6, hDl⟩ := dl_callAtA (fs := fs) (al := al) (cert := cert) hfs (K := k) (k := 5) (Or.inl rfl) (b := c)
    (leaves := rootLeaves r syms) (length_rootLeaves r syms)
    (Pre := fun rd => ReadsAt rd (ptrAt c) (rootsCells r syms))
    (fun rd _ hp => by
      have hR' := hp
      rw [rootsCells, readsAt_append] at hR'
      exact treeMem_of_reads (length_rootLeaves r syms) hR'.1)
    (fp := allocBase (al (daLevelsName 5)) e5) (c := allocBase (al (daLevelsName 5)) e5 + fs (daLevelsName 5)) le_rfl
  -- the node
  set σ := dvσ (ptrAt qb) r z (vecRets bz bt bc bo) bw c (digestHalves (daTree r 5 syms)) with hσ
  have h12 : σ (.n 12) ≠ 0 := by
    show word 1 0 + gen ^ r ≠ 0
    have := one_add_gen_pow_ne (d := r) (by omega)
    exact of_decide_eq_true (this.trans (decide_eq_true (by omega)))
  have hparts := straight_parts σ dvPre rfl
  have hal : allocs σ (dvPre.flatMap (slEvs σ)) = [128] := by
    rw [hparts.2.1]; show [logG (word 325 0)] = [128]; rw [word_g128, logG_gen_pow (by norm_num)]
  have hcalls := hparts.2.2.2
  have hroots : ∀ rd, HoldsWords rd [(c, rootsCells r syms)] → ReadsAt rd (ptrAt c) (rootsCells r syms) :=
    fun rd h => by have := readsAt_gen_pow.mp h; rwa [← ptrAt_eq_gen_pow] at this
  have hown : ∀ i, c ≤ i → i < c + 128 → ownData cert fp c "da_verify" [128] (dvPre.flatMap (slEvs σ)) i :=
    fun i h1 h2 => Or.inl ⟨(128, c), by simp [bases], h1, h2⟩
  have hcl : (dvPre.filterMap Stmt.callS).map (mkCall σ) = [⟨"da_padding", [.n 1], [.n 2], true⟩,
      ⟨"da_vector", [.n 3], [.n 4, .n 5, .n 6, .n 7], true⟩, ⟨"da_weights", [.n 5, .n 6, .n 4, .n 7], [.n 8], true⟩,
      ⟨name% «da_verify_loop0», [.n 13, .n 1, .n 8, .n 10], [], decide (σ (.n 12) ≠ 0)⟩,
      ⟨"da_pad", [.n 10, .n 1, .n 2], [], true⟩, ⟨"da_levels__L32_L5", [.n 10], [.n 14, .n 15], true⟩] := rfl
  have hb6 : e6 ≤ c + 2 ^ 38 := by
    have a1 := allocBase_le (al "da_padding") (c + 128)
    have a2 := allocBase_le (al "da_vector") e1
    have a3 := allocBase_le (al "da_weights") e2
    have a4 := allocBase_le (al Ld) e3
    have a5 := allocBase_le (al "da_pad") e4
    have a6 := allocBase_le (al name% «da_pad_loop0») (allocBase (al "da_pad") e4 + fs "da_pad")
    have a7 := allocBase_le (al (daLevelsName 5)) e5
    have f1 := hfs "da_padding"
    have f2 := hfs "da_vector"
    have f3 := hfs "da_weights"
    have f4 := hfs "da_pad"
    have f5 := hfs (daLevelsName 5)
    have l1 := lpBlk_le16' hfs Ld (r - 0)
    have l2 : padBlock fs (LeanDa.maxRows - r) ≤ (LeanDa.maxRows - r) * 2 ^ 16 + 2 ^ 16 :=
      lpBlk_le16' hfs name% «da_pad_loop0» (LeanDa.maxRows - r)
    omega
  refine ⟨e6, hb6, CallAtA.exact (callAtA_node dv_not_loop hfc ⟨σ, fn% «da_verify», dvPre.flatMap (slEvs σ),
    [.n 26, .n 27, .n 28], [(c, rootsCells r syms)], [FreePost, FreePost, FreePost, DvLPost syms 0 r, PopsNil, FreePost],
    fun rd => HoldsWords rd [(c, rootsCells r syms)], fun _ => False, find_dv, rfl,
    by rw [dv_body]; exact walk_straight σ _ dvPre rfl, ?_, ?_, ?_, ?_, ?_, fun _ h => h.elim, ?_,
    fun _ _ => trivial, ?_, ?_⟩) da_verify_exactFree⟩
  · -- the returns
    show [kecOut (dvKIns r _ _) false false 0, kecOut (dvKIns r _ _) false false 1, z] = _
    have := dv_commit (ptrAt qb) hr z (vecRets bz bt bc bo) bw c syms
    simp only [Prod.ext_iff] at this
    rw [this.1, this.2, hroot]; rfl
  · -- placed
    rw [hal]
    unfold NodeAt
    refine ⟨by rw [hparts.1]; show [σ (.n 10)] = [ofK (addressOfIndex c)]; rw [← gen_pow_eq_ofK]; rfl, ?_⟩
    intro q hq; rw [hparts.2.2.1] at hq; simp [dvPre, dvPre.dvKec, Stmt.addrS] at hq
  · rw [hal]
    exact ⟨fun q hq => by simp only [List.mem_singleton] at hq; subst hq; right; simp [length_rootsCells],
      List.pairwise_singleton _ _⟩
  · -- the count word
    intro A hA
    rw [Memory.loadAddrs_straight σ dvPre rfl] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    simp [dvPre, dvPre.dvKec, stmtLoad?] at hq
    subst hq
    exact ⟨qb + r + 0, by
      show (ptrAt qb * gen ^ r).limb 0 * _ = _; rw [ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
      Or.inr (Or.inl (by rw [Nat.add_zero]; exact hR r hr))⟩
  · intro A hA
    simp [dvPre, dvPre.dvKec, slEvs, heapHintAddrs, Ev.hintAddrs, hintDest?, h12, destHeap?] at hA
  · -- the callees
    rw [hcalls, hcl, hal]
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨Bp, e1, fun _ => False, fun _ => False, fun _ => True, fun _ h => h.elim,
      hP.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ h => h), ?_⟩
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_vector", e2, fun _ => False, vecR bz bt bc bo, fun rd => HoldsWords rd (vecWords z bz bt bc bo),
      fun _ h => h.elim, hVv.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ _ _ h => h), ?_⟩
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_weights", e3, vecR bz bt bc bo, wsR bw bcol, fun rd => HoldsWords rd (wsWords z bw bcol),
      fun i hi => Or.inr (Or.inr hi), ?_, ?_⟩
    · show CallAtA _ _ _ _ _ [σ (.n 5), σ (.n 6), σ (.n 4), σ (.n 7)] [σ (.n 8)] _ _ _ _ _ _ _ _ _
      exact hWw.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.2.2) (fun _ _ _ h => h)
    rw [KidsAtF]
    simp only [decide_eq_true h12, ↓reduceIte]
    refine ⟨lpBlk fs Ld (r - 0), e4, dvLR bw bcol c r, fun _ => False, fun _ => True, fun i hi => ?_, ?_, ?_⟩
    · rcases hi with hi | hi
      · exact Or.inr (Or.inr hi)
      · exact Or.inl (Or.inr (hown i hi.1 (by omega)))
    · have hargs : [V.n 13, .n 1, .n 8, .n 10].map σ = [gen ^ 0, gen ^ r, ptrAt bw, ptrAt c] := by
        show [word 1 0, gen ^ r, gen ^ bw, gen ^ c] = _
        rw [word_one, pow_zero, ptrAt_eq_gen_pow bw, ptrAt_eq_gen_pow c]
      rw [hargs]
      refine hL.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd hp => ⟨hp.2.2, fun j hj => ?_⟩)
        (fun _ _ _ h => h)
      rw [blobRoot_eq r syms hj]
      exact rootsCells_reads (hroots rd hp.2.1.1.1) (by omega)
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_pad", e5, padR c r (LeanDa.maxRows - r), fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inr (hown i (by unfold padR at hi; omega) (by unfold padR at hi; omega))), ?_, ?_⟩
    · have hargs : [V.n 10, .n 1, .n 2].map σ = [ptrAt c, gen ^ r, gen ^ (LeanDa.maxRows - r)] := by
        show [gen ^ c, gen ^ r, gen ^ (LeanDa.maxRows - r)] = _; rw [ptrAt_eq_gen_pow c]
      rw [hargs]
      refine hPd.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd hp j hj => ?_) (fun _ _ _ h => h)
      have := rootsCells_reads (hroots rd hp.2.1.1.1.1) (i := r + j) (by omega)
      rwa [blobLeaf, ite_neg' (by omega)] at this
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs (daLevelsName 5), e6, treeR c 5, fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inr (hown i hi.1 (by have := hi.2; norm_num at this; omega))), ?_, ?_⟩
    · have hargs : [V.n 10].map σ = [ptrAt c] := by show [gen ^ c] = _; rw [ptrAt_eq_gen_pow c]
      rw [hargs]
      show CallAtA _ _ _ _ _ _ [σ (.n 14), σ (.n 15)] _ _ _ _ _ _ _ _ _
      rw [show σ (.n 14) = (cellRoot 5 (rootLeaves r syms)).1 by rw [rootLeaves_root]; rfl,
        show σ (.n 15) = (cellRoot 5 (rootLeaves r syms)).2 by rw [rootLeaves_root]; rfl]
      exact hDl.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd hp => hroots rd hp.2.1.1.1.1.1)
        (fun _ _ _ h => h)
    rw [KidsAtF]
    exact ⟨rfl, fun _ h => h.1.1.1.1.1.1, fun _ h => h.elim⟩
  · -- the atoms
    intro rd _ hp _ ev hev
    refine events_straight (fun s hs => ?_) ev hev
    have hload : LoadHolds rd (ptrAt qb * gen ^ r) 0 (word r 0) := by
      rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hp r hr
    have hinK : IsInK (word 1 0 + gen ^ r) := by
      rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    simp only [dvPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | trivial
      | exact rfl
      | exact hload
      | exact hinK
      | (show Atom.Holds rd σ dvPre.dvKec
         exact dvK_holds (ptrAt qb) r z (vecRets bz bt bc bo) bw c _)
  · -- the entries
    intro rd ts _ _ _ hv hq
    have hlen := kidsValid_len hv
    rw [hcalls, show ((dvPre.filterMap Stmt.callS).map (mkCall σ)).length = 6 from rfl] at hlen
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨t4, _ | ⟨t5, _ | ⟨t6, _ | ⟨t7, ts⟩⟩⟩⟩⟩⟩⟩
    all_goals try (simp at hlen; done)
    rw [hcalls] at hv hq
    have h1 : FreePost rd t1 := hq.1 rfl
    have h2 : FreePost rd t2 := hq.2.1 rfl
    have h3 : FreePost rd t3 := hq.2.2.1 rfl
    have h4 : DvLPost syms 0 r rd t4 := hq.2.2.2.1 (decide_eq_true h12)
    have h5 : PopsNil rd t5 := hq.2.2.2.2.1 rfl
    have h6 : FreePost rd t6 := hq.2.2.2.2.2.1 rfl
    rw [pops_straight find_dv dv_body rfl, Tree.popsKids, Tree.popsKids, Tree.popsKids, Tree.popsKids,
      Tree.popsKids, Tree.popsKids, Tree.popsKids, dv_splice h12, h1.1, h2.1, h3.1, h4, h5, h6.1]
    simp only [List.append_nil, Nat.sub_zero, dvPops']
    rfl

end
end LeanVM.Guest.Complete
