/-
  LeanVM.Guest.Complete.MainDaWins

  `main`'s DA branch at the honest oracle: `da_verify` and the own digest's stores, or the zero stores.
-/

module

public import LeanVM.Guest.Complete.MainRest
import LeanVM.Guest.Memory.Uniform

/-!
# `main`'s DA branch

The selector `σ 384 = g^n_direct_da + g` is in `K` and zero exactly on a node checking a blob matrix
(`mOrc_384_zero`). Its arms store the own DA digest's two cells at `da_digests[n_children]`
(`mBase m 4 + 2 n_children`, `mOrc_382`): `wDa` calls `da_verify` (`MainCalleesAt.da`) and stores the
`KECCAK` of its returns (`mDa_own`), `wDaZ` stores two zeros. `runHypT_daLoads`: a run of trivial atoms
and those stores. `da_hyp`: the branch's hypotheses keep the invariant `PreInv`, the posts gaining
`qDa w` (`da_verify`'s on the checked matrix, none otherwise).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- The DA branch's post: `da_verify`'s on the checked matrix, none otherwise. -/
def qDa (w : NodeWitness) : List (Reader → Tree → Prop) :=
  match w.daMatrix with
  | some (c, mw) => [PopsPost (Prover.daHints c mw)]
  | none => []

/-- A store of the own DA digest's cell `i` from the value `b + i`. -/
def daLoad (b : ℕ) : Atom → Bool
  | .load (.n d) (.n 382) i => decide (d = b + i) && decide (i < 2)
  | _ => false

set_option maxRecDepth 200000 in
theorem mPre_da_mem : Atom.mul (.n 381) (.n 6) (.n 6) ∈ atomsOf mPre ∧
    Atom.mul (.n 382) (.n 380) (.n 381) ∈ atomsOf mPre ∧ Atom.const (.n 383) (word 2 0) ∈ atomsOf mPre ∧
    Atom.add (.n 384) (.n 7) (.n 383) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem da_shapes :
    ((atomsOf ((mDa.drop 1).take 9)).all (fun a => noHeapB a && (trivPM a || daLoad 394 a)) = true ∧
      allocDsts ((atomsOf ((mDa.drop 1).take 9)).map Ev.atom) = [] ∧
      (atomsOf ((mDa.drop 1).take 9)).filter isAllocA = []) ∧
    ((atomsOf ((mDaZ.drop 0).take 4)).all (fun a => noHeapB a && (trivPM a || daLoad 396 a)) = true ∧
      allocDsts ((atomsOf ((mDaZ.drop 0).take 4)).map Ev.atom) = [] ∧
      (atomsOf ((mDaZ.drop 0).take 4)).filter isAllocA = []) ∧
    Atom.const (.n 396) (word 0 0) ∈ atomsOf mDaZ ∧ Atom.const (.n 397) (word 0 0) ∈ atomsOf mDaZ := by
  decide +kernel

theorem mBase_five_le (m : MainCounts) : mBase m 5 ≤ mTop m := by
  rw [mBase_five, mBase_four, mBase_three]
  simp only [mTop, MainCounts.bufs, List.sum_cons, List.sum_nil]
  omega

theorem mBase_four_ge (m : MainCounts) : B2C.fs "main" ≤ mBase m 4 := by
  rw [mBase_four, mBase_three]; omega

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd0 : Reader}
  {R : ℕ → Prop} {es : List Ev}

/-- **The own DA digest's slot**: `da_digests + 2 n_children`. -/
theorem mOrc_382 :
    mVal rd0 (mOrc al s w) (.n 382) = ptrAt (mBase (mainCounts s w) 4 + 2 * (mainCounts s w).nc) := by
  obtain ⟨m381, m382, -, -⟩ := mPre_da_mem
  have c6 := (mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)).2.2.2.2.2.2.1
  have e381 := pmul (good_mul (mPre_good m381) (by norm_num) (by norm_num)) c6 c6
  have e382 : mVal rd0 (mOrc al s w) (.n 382) = mVal rd0 (mOrc al s w) (.n 380) * mVal rd0 (mOrc al s w) (.n 381) :=
    good_mul (mPre_good m382) (by norm_num) (by norm_num)
  rw [e382, mOrc_380, e381]
  simp only [mPtr, Nat.add_zero, ptrAt_mul_pow, two_mul]

/-- The selector: `g^n_direct_da + g`. -/
theorem mOrc_384 : mVal rd0 (mOrc al s w) (.n 384) = gen ^ (mainCounts s w).nd + gen := by
  obtain ⟨-, -, m383, m384⟩ := mPre_da_mem
  have c7 := (mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)).2.2.2.2.2.2.2
  have e384 : mVal rd0 (mOrc al s w) (.n 384) = mVal rd0 (mOrc al s w) (.n 7) + mVal rd0 (mOrc al s w) (.n 383) :=
    mPre_good m384
  have e383 : mVal rd0 (mOrc al s w) (.n 383) = word 2 0 := mPre_good m383
  rw [e384, e383, c7, word_gen]

/-- **The selector is zero exactly on a node checking a blob matrix.** -/
theorem mOrc_384_zero : mVal rd0 (mOrc al s w) (.n 384) = 0 ↔ (mainCounts s w).nd = 1 := by
  rw [mOrc_384, CharTwo.add_eq_zero]
  have hd := nd_le s w
  constructor
  · intro h
    by_contra hne
    have h0 : (mainCounts s w).nd = 0 := by omega
    rw [h0, pow_zero] at h
    have := (guard_eq_zero_iff (n := 1) (by norm_num)).mp (by rw [word_one, pow_one, h, CharTwo.add_self_eq_zero])
    omega
  · intro h; rw [h, pow_one]

theorem mOrc_384_inK : IsInK (mVal rd0 (mOrc al s w) (.n 384)) := by
  rw [mOrc_384]
  exact isInK_add (gen_pow_isInK _) (by simpa using gen_pow_isInK 1)

/-- **A run of trivial atoms and the own DA digest's stores** from the values `b`, `b + 1`. -/
theorem runHypT_daLoads {as : List Atom} {b a : ℕ} {D : ℕ → Prop} {O : Reader → Prop}
    (hall : as.all (fun x => noHeapB x && (trivPM x || daLoad b x)) = true)
    (hdst : allocDsts (as.map Ev.atom) = []) (hal : as.filter isAllocA = [])
    (hv : ∀ i < 2, mVal rd0 (mOrc al s w) (.n (b + i)) = (ownDaCells w).getD i 0)
    (hO : ∀ rd, O rd → HoldsWords rd (mainWords s w cover)) :
    RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) a
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R D (mainPreR s) O as := by
  have hq : ∀ x ∈ as, noHeapB x = true ∧ (trivPM x = true ∨ daLoad b x = true) := fun x hx => by
    have := List.all_eq_true.mp hall x hx
    simpa only [Bool.and_eq_true, Bool.or_eq_true] using this
  have hstore : ∀ x, daLoad b x = true → ∃ i, i < 2 ∧ x = .load (.n (b + i)) (.n 382) i := by
    intro x hx
    match x, hx with
    | .load (.n d) (.n 382) i, hx =>
      simp only [daLoad, Bool.and_eq_true, decide_eq_true_eq] at hx
      exact ⟨i, hx.2, by rw [hx.1]⟩
  have hlt := mBase_five_le (mainCounts s w)
  have h5 := mBase_five (mainCounts s w)
  have h4 := mBase_four_ge (mainCounts s w)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_atoms, hal]; rfl
  · intro A hA
    obtain ⟨x, hx, hl⟩ := loadAddr_mem hA
    rcases (hq x hx).2 with ht | ht
    · exfalso
      cases x with
      | load d p off => simp [trivPM] at ht
      | _ => simp [Ev.loadAddr?] at hl
    · obtain ⟨i, hi, rfl⟩ := hstore x ht
      simp only [Ev.loadAddr?, Option.some.injEq, mOrc_382] at hl
      rw [Main.addr_ofK] at hl
      exact ⟨_, hl.symm, Or.inl (own_main (by omega) (by omega))⟩
  · rw [heapHintAddrs_noHeap (List.all_eq_true.mpr fun x hx => (hq x hx).1)]
    intro A hA; simp at hA
  · intro x hx
    rcases (hq x hx).2 with ht | ht
    · exact pureT_triv ht
    · obtain ⟨i, hi, rfl⟩ := hstore x ht
      trivial
  · intro rd _ _ hOr x hx
    rcases (hq x hx).2 with ht | ht
    · exact memT_triv ht
    · obtain ⟨i, hi, rfl⟩ := hstore x ht
      show LoadHolds rd _ i _
      rw [mOrc_382, hv i hi]
      have hw := (hO rd hOr) (mBase (mainCounts s w) 4,
        w.children.flatMap (fun ch => Prover.digestCells ch.statement.claims.daDigest) ++ ownDaCells w)
        (by simp only [mainWords]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
      have h2 := (readsAt_append'.mp hw).2
      rw [dFlat_length, ptrAt_mul_pow] at h2
      have hl : i < (ownDaCells w).length := by rw [ownDaCells_length]; exact hi
      rw [List.getD_eq_getElem _ _ hl]
      exact h2 i hl

/-- **The DA branch's hypotheses** keep the invariant, the posts gaining `qDa w`. -/
theorem da_hyp {st : St} {K : St → Prop} {a : ℕ} {Qs : List (Reader → Tree → Prop)}
    (hcl : MainCalleesAt al k s w cover) (hst : PreInv al s w cover a Qs st)
    (hrest : ∀ st', PreInv al s w cover a (Qs ++ qDa w) st' → K st') :
    IteHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (.n 384) wDa wDaZ st K := by
  obtain ⟨⟨t1, d1, f1⟩, ⟨t2, d2, f2⟩, k396, k397⟩ := da_shapes
  have hO : ∀ rd, st.O rd → HoldsWords rd (mainWords s w cover) := fun rd h => (hst.hO rd h).1
  refine ⟨mOrc_384_inK, fun h0 => ?_, fun h0 => ?_⟩
  · have hnd := mOrc_384_zero.mp h0
    obtain ⟨⟨c, mw⟩, hm⟩ : ∃ p, w.daMatrix = some p := by
      cases hc : w.daMatrix with
      | none => simp [mainCounts, hc] at hnd
      | some p => exact ⟨p, rfl⟩
    have hr : ∀ v ∈ [V.n 385, V.n 386, V.n 387], mVal rd0 (mOrc al s w) v = mOrc al s w v.idx :=
      mVal_goodDa (rd := rd0) (w := mOrc al s w) h0 (.call "da_verify" [.n 66] [.n 385, .n 386, .n 387])
        (by rw [← wDa_flat]; exact mem_flat_call List.mem_cons_self)
    have o5 : mOrc al s w 385 = (daRets w).getD 0 0 := rfl
    have o6 : mOrc al s w 386 = (daRets w).getD 1 0 := rfl
    have o7 : mOrc al s w 387 = (daRets w).getD 2 0 := rfl
    have r385 : mVal rd0 (mOrc al s w) (.n 385) = (digestHalves c.daRoot).1 := by
      rw [hr _ (by simp)]; show mOrc al s w 385 = _; rw [o5]; simp [daRets, hm, Prover.digestCells]
    have r386 : mVal rd0 (mOrc al s w) (.n 386) = (digestHalves c.daRoot).2 := by
      rw [hr _ (by simp)]; show mOrc al s w 386 = _; rw [o6]; simp [daRets, hm, Prover.digestCells]
    have r387 : mVal rd0 (mOrc al s w) (.n 387) = c.membershipChallenge := by
      rw [hr _ (by simp)]; show mOrc al s w 387 = _; rw [o7]; simp [daRets, hm, Prover.digestCells]
    have hown := mDa_own ⟨mw, hm⟩ h0 r385 r386 r387
    unfold wDa mDa_w0 mDa_w1
    refine winsHypT_callI hst rfl ?_ ?_ (hcl.da c mw hm) (by norm_num) (fs_add_le _) fun st1 hst1 => ?_
    · simp only [argsOf, List.map_cons, List.map_nil, w9_ptr, mPtr, Nat.add_zero]
    · simp only [retsOf, List.map_cons, List.map_nil, r385, r386, r387, Prover.digestCells, List.cons_append,
        List.nil_append]
    refine winsHypT_runI (a' := a) hst1 (by simp only [allocs_atoms, f1, List.filterMap_nil, List.sum_nil, Nat.add_zero])
      (runHypT_daLoads t1 d1 f1 (fun i hi => ?_) fun rd h => (hst1.hO rd h).1) fun st2 hst2 => ?_
    · rw [← hown]
      rcases i with _ | _ | i
      · simp
      · simp
      · omega
    rw [WinsHypT]
    refine hrest st2 ?_
    have e : qDa w = [PopsPost (Prover.daHints c mw)] := by simp [qDa, hm]
    rw [e]; exact hst2
  · have hnd : (mainCounts s w).nd ≠ 1 := fun h => h0 (mOrc_384_zero.mpr h)
    have hm : w.daMatrix = none := by
      cases hc : w.daMatrix with
      | none => rfl
      | some p => simp [mainCounts, hc] at hnd
    have hz := mVal_goodDaZ (rd := rd0) (w := mOrc al s w) h0
    have z396 : mVal rd0 (mOrc al s w) (.n 396) = 0 :=
      (hz _ (atom_mem_of_atomsOf k396)).trans word_zero
    have z397 : mVal rd0 (mOrc al s w) (.n 397) = 0 :=
      (hz _ (atom_mem_of_atomsOf k397)).trans word_zero
    unfold wDaZ mDaZ_w0
    refine winsHypT_runI (a' := a) hst (by simp only [allocs_atoms, f2, List.filterMap_nil, List.sum_nil, Nat.add_zero])
      (runHypT_daLoads t2 d2 f2 (fun i hi => ?_) hO) fun st1 hst1 => ?_
    · interval_cases i
      · simp [z396, ownDaCells, hm]
      · simp [z397, ownDaCells, hm]
    rw [WinsHypT]
    refine hrest st1 ?_
    have e : qDa w = [] := by simp [qDa, hm]
    rw [e, List.append_nil]; exact hst1

end

end
end LeanVM.Guest.Complete
