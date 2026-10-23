/-
  LeanVM.Guest.B1.Whir.OsKidsA

  `open_stacked`'s callees before each level's positions, complete on the caller's words.
-/

module

public import LeanVM.Guest.B1.Whir.OsBodyMemOf
public import LeanVM.Guest.B1.Whir.OsCallees

/-!
# The callees before the positions (TRIAGE #36)

On the caller's words `Lk` (its own words and buffers), at their honest arguments and returns:
`opening_fold` (the words read at the cursor), the final message (the words read, stored in its
buffer), `assert_canonical` (the next root's scalars, canonical as the root decodes),
`opening_ood_point` (the point stored in its buffer), `grind_check` (the nonce's proof of work).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- A callee complete on the words `Lk`, returning its frame's words. -/
def osKC (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Lk : Main.Layout) : CallRel :=
  fun f a r => CompleteAtD fs cert κ f Lk a (Returns r)

theorem os_readsAt_shift {rd : Reader} {cur : E} {xs : List E} (h : ReadsAt rd cur xs) {p n : ℕ}
    (hp : p + n ≤ xs.length) : ReadsAt rd (cur * gen ^ p) ((xs.drop p).take n) := by
  intro k hk
  simp only [List.length_take, List.length_drop] at hk
  rw [loadHolds_mul_gen_pow, List.getElem_take, List.getElem_drop]
  exact h (p + k) (by omega)

/-- **Words every defined-low memory holding `Lin` holds, every memory holding `Lin` holds.** -/
theorem os_reads_noLow {Lin : Main.Layout} {p : E} {xs : List E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd p xs) {rd : Reader} (hL : MemL rd Lin) :
    ReadsAt rd p xs := by
  let rd' : Reader := fun A => match rd A with | some v => some v | none => some 0
  have hsome : ∀ A v, rd A = some v → rd' A = some v := fun A v h => by simp only [rd', h]
  have hlow : LowDef κ rd' := fun i _ => by
    simp only [rd']; split <;> rfl
  have hL' : MemL rd' Lin := fun q hq k hk => ⟨(hL q hq k hk).1, hsome _ _ (hL q hq k hk).2⟩
  intro k hk
  have h' := hall rd' hlow hL' k hk
  obtain ⟨i, hi, q, hq, h1, h2⟩ := os_addr_in_regionL (A := p.limb 0 * Parameters.gpow k) (v := xs[k])
    (fun rd2 hl2 hm2 => (hall rd2 hl2 hm2 k hk).2) hlow hL'
  have hc := (hL q hq (i - q.1) (by omega)).2
  rw [Main.addr_ofK, show q.1 + (i - q.1) = i by omega] at hc
  obtain ⟨v, hv⟩ : ∃ v, rd (Parameters.gpow i) = some v := ⟨_, hc⟩
  refine ⟨h'.1, ?_⟩
  have e := h'.2
  rw [hi, hsome _ _ hv] at e
  rw [hi, hv, e]

/-- **`opening_fold`** at the cursor's words. -/
theorem os_kid_fold (hf : OsFoldAtD fs cert κ) {Lk : Main.Layout} {xs : List E} {cur : E}
    (hM : ∀ rd, LowDef κ rd → MemL rd Lk → ReadsAt rd cur xs) (cv' : Digest) (p' : ℕ) (q' : List E)
    (hq : q'.length = 3) (hp : p' + 2 ≤ xs.length) :
    osKC fs cert κ Lk "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0,
      q'.getD 1 0, q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p')) := by
  obtain ⟨c0, c1, c2, rfl⟩ : ∃ c0 c1 c2, q' = [c0, c1, c2] := by
    match q', hq with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  refine hf _ _ Lk fun rd hl hm => ?_
  have hr := os_readsAt_shift (hM rd hl hm) (p := p') (n := 2) hp
  have e : (xs.drop p').take 2 = [xs.getD p' 0, xs.getD (p' + 1) 0] := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    have hi : i < 2 := by simpa using h2
    interval_cases i <;> simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show p' < xs.length by omega),
      List.getElem?_eq_getElem (show p' + 1 < xs.length by omega)]
  rw [e] at hr
  exact ⟨cv', _, _, _, _, _, _, rfl, hr, runsTo_foldStep cv' c0 c1 c2 (xs.getD p' 0) (xs.getD (p' + 1) 0), rfl⟩

/-- **The final message**, read at the cursor and stored at `out`. -/
theorem os_kid_final {name : String} {n : ℕ} (hfm : OsFinalMsgAtD fs cert κ name n) {Lk : Main.Layout} {xs : List E}
    {cur out : E} {P1 : ℕ} (hn : P1 + n ≤ xs.length)
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd cur xs ∧ ReadsAt rd out ((xs.drop P1).take n))
    (cv1 : Digest) :
    osKC fs cert κ Lk name [(digestScalars cv1).1, (digestScalars cv1).2, cur * gen ^ P1, out]
      [(digestScalars (obsAll cv1 ((xs.drop P1).take n))).1, (digestScalars (obsAll cv1 ((xs.drop P1).take n))).2,
        cur * gen ^ (P1 + n)] := by
  have hl : ((xs.drop P1).take n).length = n := by simp; omega
  refine hfm _ _ Lk fun rd hm => ?_
  obtain ⟨hx, ho⟩ := hM rd hm
  refine ⟨cv1, _, obsAll cv1 ((xs.drop P1).take n), rfl, hl, os_readsAt_shift hx hn, ho, ?_, ?_⟩
  · have := runsTo_readN cv1 ((xs.drop P1).take n)
    rwa [hl] at this
  · rw [mul_assoc, ← pow_add]

theorem os_canonical_of_digest {s : E × E} {dg : Digest} (h : digestOfScalars s = some dg) :
    IsCanonical128 s.1 ∧ IsCanonical128 s.2 := by
  unfold digestOfScalars at h
  split at h
  · assumption
  · cases h

/-- **`assert_canonical`** on a canonical word. -/
theorem os_kid_canonical (hc : OsAssertCanonicalAtD fs cert κ) (Lk : Main.Layout) {w : E} (hw : IsCanonical128 w) :
    osKC fs cert κ Lk "assert_canonical" [w] [0] :=
  hc _ _ Lk fun _ _ _ => ⟨hw, rfl⟩

/-- **`opening_ood_point`**, its `m` samples stored at `point`. -/
theorem os_kid_ood (ho : OsOodPointAtD fs cert κ) {Lk : Main.Layout} {cv : Digest} {point : E} {m : ℕ}
    (hm0 : 0 < m) (hm : 2 * m + 2 < ordG) (hM : ∀ rd, LowDef κ rd → MemL rd Lk → ReadsAt rd point (sqAll m cv).1) :
    osKC fs cert κ Lk "opening_ood_point" [(digestScalars cv).1, (digestScalars cv).2, point, gen ^ m]
      [(digestScalars (sqAll m cv).2).1, (digestScalars (sqAll m cv).2).2] :=
  ho _ _ Lk fun rd hl hmm => ⟨m, by omega, hm, rfl,
    Or.inr ⟨hm0, cv, _, _, rfl, runsTo_sampleN m cv, hM rd hl hmm, rfl⟩⟩

/-- **`grind_check`** on a nonce with its proof of work. -/
theorem os_kid_grind (hg : OsGrindAtD fs cert κ) (Lk : Main.Layout) (cv : Digest) (nonce : E) {m : ℕ} (hm : m ≤ 64)
    (hp : powOk m nonce (gcDigest cv nonce) = true) :
    osKC fs cert κ Lk "grind_check" [(digestScalars cv).1, (digestScalars cv).2, nonce, gen ^ m] [] :=
  hg _ _ Lk fun _ _ _ => ⟨rfl, m, by simp only [ordG]; omega, hm, rfl, cv, rfl, hp⟩

end
end LeanVM.Guest.B1
