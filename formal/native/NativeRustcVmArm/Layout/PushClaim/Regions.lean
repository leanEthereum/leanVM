module

public import NativeRustcVmArm.Layout.PushClaim.Exec
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `push_claim`'s regions

With `n < 160` claims at `c`: the frame `sb` (the 48 bytes below the entry's SP), the count word
`c`, the next claim `slot c n` (608 bytes at `c + 8 + 608 n`). They are data memory, do not wrap,
are apart (`regions_wf`), inside the claims or the frame (`inRegions_out`); a range apart from the
claims and the frame is apart from each (`not_inRegions`); an earlier claim is apart from the
count word and the next claim (`not_inRegions_old`).
-/

namespace NativeRustcVmArm.Layout.PushClaim

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Layout


public section

/-- The next claim's address. -/
abbrev slot (c : BitVec 64) (n : Nat) : BitVec 64 := c + BitVec.ofNat 64 (8 + 608 * n)

/-- The three regions. -/
abbrev regions (sb c : BitVec 64) (n : Nat) : List (BitVec 64 × Nat) :=
  [(sb, 48), (c, 8), (slot c n, 608)]

theorem toNat_slot {c : BitVec 64} {n : Nat} (hc : NoWrap c claimsBytes) (hn : n < 160) :
    (slot c n).toNat = c.toNat + 8 + 608 * n := by
  unfold NoWrap claimsBytes columnClaimBytes claimCap at hc
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega

/-- The regions are an environment's. -/
theorem regions_wf {d : Mem 64} {sb c : BitVec 64} {n : Nat} (hsm : Mapped d sb 48)
    (hsn : NoWrap sb 48) (hcm : Mapped d c claimsBytes) (hcn : NoWrap c claimsBytes)
    (hcs : Apart c claimsBytes sb 48) (hn : n < 160) :
    AllOf (fun e : BitVec 64 × Nat ↦ Mapped d e.1 e.2 ∧ NoWrap e.1 e.2) (regions sb c n) ∧
      (regions sb c n).Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2 := by
  have hs := toNat_slot hcn hn
  unfold NoWrap claimsBytes columnClaimBytes claimCap at hcn
  unfold Apart claimsBytes columnClaimBytes claimCap at hcs
  have hcm8 : Mapped d c 8 := NativeRustcVm.Mapped.mono hcm (by decide)
  have hsl : Mapped d (slot c n) 608 :=
    NativeRustcVm.Mapped.sub hcm (show 8 + 608 * n + 608 ≤ claimsBytes by
      unfold claimsBytes columnClaimBytes claimCap; omega)
  have h1 : NoWrap c 8 := by unfold NoWrap; omega
  have h2 : NoWrap (slot c n) 608 := by unfold NoWrap; omega
  refine ⟨⟨⟨hsm, hsn⟩, ⟨hcm8, h1⟩, ⟨hsl, h2⟩, trivial⟩, ?_⟩
  have a1 : Apart sb 48 c 8 := by unfold Apart; omega
  have a2 : Apart sb 48 (slot c n) 608 := by unfold Apart; omega
  have a3 : Apart c 8 (slot c n) 608 := by unfold Apart; omega
  exact List.Pairwise.cons (by simp [a1, a2]) (List.Pairwise.cons (by simp [a3])
    (List.pairwise_singleton _ _))

/-- Where the regions are: in the claims or the frame. -/
theorem inRegions_out {sb c : BitVec 64} {n : Nat} (hcn : NoWrap c claimsBytes)
    (hn : n < 160) {p : BitVec 64} (h : InRegions (regions sb c n) p) :
    InRange c claimsBytes p ∨ InRange sb 48 p := by
  have hs := toNat_slot hcn hn
  obtain ⟨e, he, hp⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  unfold NoWrap claimsBytes columnClaimBytes claimCap at hcn
  rcases he with rfl | rfl | rfl
  · exact .inr hp
  · left
    dsimp only at hp
    rw [Sym.inRange_iff (by omega)] at hp
    rw [Sym.inRange_iff (by unfold claimsBytes columnClaimBytes claimCap; omega)]
    unfold claimsBytes columnClaimBytes claimCap; omega
  · left
    dsimp only at hp
    rw [Sym.inRange_iff (by omega)] at hp
    rw [Sym.inRange_iff (by unfold claimsBytes columnClaimBytes claimCap; omega)]
    unfold claimsBytes columnClaimBytes claimCap; omega

/-- A range apart from the claims and the frame is apart from the regions. -/
theorem not_inRegions {sb c a : BitVec 64} {n len : Nat} (hsn : NoWrap sb 48)
    (hcn : NoWrap c claimsBytes) (hn : n < 160) (han : NoWrap a len)
    (hac : Apart a len c claimsBytes) (has : Apart a len sb 48) {j : Nat} (hj : j < len) :
    ¬InRegions (regions sb c n) (a + BitVec.ofNat 64 j) := fun h ↦ by
  rcases inRegions_out hcn hn h with h | h
  · exact NativeRustcVm.Apart.not_inRange_add hac han hcn hj h
  · exact NativeRustcVm.Apart.not_inRange_add has han hsn hj h

/-- An earlier claim is apart from the count word and the next claim, and from the frame. -/
theorem not_inRegions_old {sb c : BitVec 64} {n i : Nat} (hsn : NoWrap sb 48)
    (hcn : NoWrap c claimsBytes) (hcs : Apart c claimsBytes sb 48) (hn : n < 160) (hi : i < n)
    {j : Nat} (hj : j < 608) :
    ¬InRegions (regions sb c n) (c + BitVec.ofNat 64 (8 + 608 * i) + BitVec.ofNat 64 j) := by
  have hs := toNat_slot hcn hn
  unfold NoWrap claimsBytes columnClaimBytes claimCap at hcn
  unfold Apart claimsBytes columnClaimBytes claimCap at hcs
  rw [NativeRustcVm.addr_add_add]
  have hp : (c + BitVec.ofNat 64 (8 + 608 * i + j)).toNat = c.toNat + (8 + 608 * i + j) :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rintro ⟨e, he, h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · dsimp only at h; rw [Sym.inRange_iff hsn] at h; omega
  · dsimp only at h; rw [Sym.inRange_iff (by omega)] at h; omega
  · dsimp only at h; rw [Sym.inRange_iff (by omega)] at h; omega

end

end NativeRustcVmArm.Layout.PushClaim
