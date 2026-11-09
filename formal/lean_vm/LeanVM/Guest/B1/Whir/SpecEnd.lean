/-
  LeanVM.Guest.B1.Whir.SpecEnd

  The honest trace's levels with their caps: every level's openings agree (`CapsAgree`) and climb
  to its root, so the honest cap of `SpecCaps` serves it.
-/

module

public import LeanVM.Guest.B1.Whir.SpecTrace
public import LeanVM.Guest.B1.Whir.SpecCaps
public import LeanVM.Guest.AcceptableChild

/-!
# The levels' caps

For a level `L` of the honest trace (`nz_trace`):

* `SpLv.qs_lt`: its positions lie below `2^D`;
* `SpLv.batchOpens`: its openings at its positions climb to its root (`L.Ok`), when the tree's
  height is `D` (the configuration's fact `lv.depth = ml + logInvRate`);
* `SpLv.batchAgrees`: they agree wherever they meet, by `CapsAgree` (they are a query step of the
  run);
* `SpLv.cap_meaning`, `SpLv.cap_writes`: so the honest cap of the step (`capCell`, `capFl`) is
  checked by `verify_merkle_cap` and agrees with the queries' writes (`cap_meaning`,
  `cap_writes`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace SpLv

variable (L : SpLv)

theorem qs_length : L.qs.length = L.level.queries := by simp [SpLv.qs, queriesOf]

theorem qs_lt : ∀ q ∈ L.qs, q < 2 ^ L.D := by
  intro q hq
  simp only [SpLv.qs, queriesOf, List.mem_map, List.mem_range] at hq
  obtain ⟨k, -, rfl⟩ := hq
  exact Nat.mod_lt _ (by positivity)

/-- The level's query step: its positions with its openings. -/
abbrev batch : List (ℕ × Opening) := L.qs.zip L.os

theorem mem_batch {a : ℕ × Opening} (ha : a ∈ L.batch) :
    ∃ k, ∃ (hk : k < L.qs.length) (ho : k < L.os.length), a = (L.qs[k], L.os[k]) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
  simp only [List.length_zip] at hk
  exact ⟨k, by omega, by omega, by simp⟩

/-- **The level's openings climb to its root.** -/
theorem batchOpens {R : List (Digest × ℕ × ℕ)} {d : Digest} (hOk : L.Ok R d) (hh : L.height = L.D) :
    BatchOpens L.height L.root L.batch := by
  intro a ha
  obtain ⟨k, hk, ho, rfl⟩ := L.mem_batch ha
  obtain ⟨-, hlen, hcl⟩ := openOne_facts (hOk.opens k hk ho)
  exact ⟨by rw [hh]; exact L.qs_lt _ (List.getElem_mem hk), hlen, hcl⟩

/-- **The level's openings agree**: they are a query step of the run. -/
theorem batchAgrees {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E} {os : List (List Opening)}
    {root : Digest} (hcaps : CapsAgree μ r target S xs os root)
    (hm : (L.height, L.qs.zip L.os) ∈ queryStepsOf (whirOpen μ r target) (osStart μ r S xs os root)) :
    BatchAgrees L.height L.batch :=
  hcaps _ hm

/-- **The level's honest cap is checked** by `verify_merkle_cap`. -/
theorem cap_meaning {R : List (Digest × ℕ × ℕ)} {d : Digest} (hOk : L.Ok R d)
    (hh : L.height = L.D) (hag : BatchAgrees L.height L.batch) (hq : 1 ≤ L.level.queries)
    {cd : ℕ} (hcd : 2 ≤ cd) (hcdd : cd ≤ L.height) {rd : Reader} {cap flags : E}
    (hcap : ∀ k, 2 ≤ k → k < 2 ^ (cd + 2) → LoadHolds rd cap k (capCell L.height L.batch k))
    (hfl : ∀ k, 2 ≤ k → k < 2 ^ cd → LoadHolds rd flags k (capFl L.height L.batch cd k)) :
    MeaningVerifyMerkleCap cd rd [cap, flags] [(digestHalves L.root).1, (digestHalves L.root).2] := by
  refine Whir.cap_meaning hcd hcdd (L.batchOpens hOk hh) hag ?_ hcap hfl
  intro h
  have : L.batch.length = L.qs.length := by
    simp only [List.length_zip, hOk.osLen, min_self]
  rw [h, List.length_nil, qs_length] at this
  omega

/-- **The queries' writes agree with the level's honest cap.** -/
theorem cap_writes {R : List (Digest × ℕ × ℕ)} {d : Digest} (hOk : L.Ok R d)
    (hh : L.height = L.D) (hag : BatchAgrees L.height L.batch)
    {cd : ℕ} (hcd : 2 ≤ cd) (hcdd : cd ≤ L.height) {rd : Reader} {cap flags : E}
    (hcap : ∀ k, 2 ≤ k → k < 2 ^ (cd + 2) → LoadHolds rd cap k (capCell L.height L.batch k))
    (hfl : ∀ k, 2 ≤ k → k < 2 ^ cd → LoadHolds rd flags k (capFl L.height L.batch cd k))
    (k : ℕ) (hk : k < L.qs.length) (ho : k < L.os.length) :
    LoadHolds rd cap (2 * (2 ^ cd + L.qs[k] / 2 ^ (L.height - cd)))
        (digestHalves (climbD (merkleLeafDigest L.os[k].leaf) L.qs[k]
          (L.os[k].path.take (L.height - cd)))).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + L.qs[k] / 2 ^ (L.height - cd)) + 1)
        (digestHalves (climbD (merkleLeafDigest L.os[k].leaf) L.qs[k]
          (L.os[k].path.take (L.height - cd)))).2 ∧
      LoadHolds rd flags (2 ^ (cd - 1) + L.qs[k] / 2 ^ (L.height - cd + 1)) 1 :=
  Whir.cap_writes (a := (L.qs[k], L.os[k])) hcd hcdd (L.batchOpens hOk hh) hag hcap hfl
    (List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩)

end SpLv

end
end LeanVM.Guest.B1.Whir
