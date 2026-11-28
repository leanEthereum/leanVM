/-
  LeanVM.Guest.B1.VerifySub.Reads

  `verify_sub`'s front: the seed, the announced words, the root's words.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.Digest.Range
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The seed, the announced words, the root

`vsSeedT` (statements `18 .. 23`) and `vsReadsT` (`37 .. 105`), checked against the body by the
kernel. `phSeed`: the seed's permutation writes the seed state's capacity. `ReadsFacts`, from
`vsReadsT`: the eight announced words and the root's two at `stream`, absorbed from the seed's
capacity (`vsF0` to `vsF1`, then `vsF2`), and the two words `g_power_of_word` reads. `phRoot`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s statements 18 to 23. -/
def vsSeedT : List Stmt := (
  .atom (.const (.n 24) (word 1 0)) ::
  .atom (.const (.n 25) (word 0 0)) ::
  .atom (.const (.n 26) (word 0 0)) ::
  .atom (.const (.n 27) (word 0 0)) ::
  .atom (.const (.n 28) (word 0 0)) ::
  .atom (.keccak [.n 2, .n 3, .n 0, .n 1, .n 25, .n 26, .n 27, .n 28, .n 25, .n 25, .n 26, .n 27, .n 28] [.n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38, .n 39, .n 40, .n 41] false false) ::
  [])

theorem vsSeedT_eq : (vsPre.drop 18).take 6 = vsSeedT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 37 to 105. -/
def vsReadsT : List Stmt := (
  .atom (.hint (.alloc (.n 56) 6)) ::
  .atom (.load (.n 57) (.n 55) 0) ::
  .atom (.copy (.n 58) (.n 57)) ::
  .atom (.const (.n 59) (word 0 1)) ::
  .atom (.load (.n 60) (.n 55) 1) ::
  .atom (.copy (.n 61) (.n 60)) ::
  .atom (.const (.n 62) (word 0 1)) ::
  .atom (.load (.n 60) (.n 56) 0) ::
  .atom (.load (.n 63) (.n 55) 2) ::
  .atom (.copy (.n 64) (.n 63)) ::
  .atom (.const (.n 65) (word 0 1)) ::
  .atom (.load (.n 63) (.n 56) 1) ::
  .atom (.load (.n 66) (.n 55) 3) ::
  .atom (.copy (.n 67) (.n 66)) ::
  .atom (.const (.n 68) (word 0 1)) ::
  .atom (.load (.n 66) (.n 56) 2) ::
  .atom (.keccak [.n 58, .n 59, .n 61, .n 62, .n 64, .n 65, .n 67, .n 68, .n 37, .n 38, .n 39, .n 40, .n 41] [.n 69, .n 70, .n 71, .n 72, .n 73, .n 74, .n 75, .n 76, .n 77, .n 78, .n 79, .n 80, .n 81] false false) ::
  .atom (.load (.n 82) (.n 55) 4) ::
  .atom (.copy (.n 83) (.n 82)) ::
  .atom (.const (.n 84) (word 0 1)) ::
  .atom (.load (.n 82) (.n 56) 3) ::
  .atom (.load (.n 85) (.n 55) 5) ::
  .atom (.copy (.n 86) (.n 85)) ::
  .atom (.const (.n 87) (word 0 1)) ::
  .atom (.load (.n 85) (.n 56) 4) ::
  .atom (.load (.n 88) (.n 55) 6) ::
  .atom (.copy (.n 89) (.n 88)) ::
  .atom (.const (.n 90) (word 0 1)) ::
  .atom (.load (.n 88) (.n 56) 5) ::
  .atom (.load (.n 91) (.n 55) 7) ::
  .atom (.copy (.n 92) (.n 91)) ::
  .atom (.const (.n 93) (word 0 1)) ::
  .call "g_power_of_word" [.n 91] [.n 94] ::
  .atom (.const (.n 95) (word 2 0)) ::
  .atom (.mul (.n 94) (.n 96) (.n 95)) ::
  .atom (.const (.n 97) (word 8 0)) ::
  .atom (.rangeCheck (.n 96) (.n 98) (.n 99) (.n 100) (.n 97)) ::
  .call "g_power_of_word" [.n 57] [.n 101] ::
  .atom (.const (.n 102) (word 1073741824 0)) ::
  .atom (.rangeCheck (.n 101) (.n 103) (.n 104) (.n 105) (.n 102)) ::
  .atom (.const (.n 106) (word 4294967296 0)) ::
  .atom (.const (.n 107) (word 2 0)) ::
  .atom (.mul (.n 101) (.n 108) (.n 107)) ::
  .atom (.rangeCheck (.n 108) (.n 109) (.n 110) (.n 111) (.n 106)) ::
  .atom (.hint (.witness "table_logs" (.heap (.n 6) 0 6))) ::
  .atom (.hint (.alloc (.n 112) 8)) ::
  .atom (.const (.n 113) (word 1 0)) ::
  .atom (.copy (.n 114) (.n 101)) ::
  .atom (.load (.n 115) (.n 6) 0) ::
  .atom (.load (.n 116) (.n 6) 1) ::
  .atom (.load (.n 117) (.n 6) 2) ::
  .atom (.load (.n 118) (.n 6) 3) ::
  .atom (.load (.n 119) (.n 6) 4) ::
  .atom (.load (.n 120) (.n 6) 5) ::
  .atom (.load (.n 113) (.n 112) 0) ::
  .atom (.load (.n 114) (.n 112) 1) ::
  .atom (.load (.n 115) (.n 112) 2) ::
  .atom (.load (.n 116) (.n 112) 3) ::
  .atom (.load (.n 117) (.n 112) 4) ::
  .atom (.load (.n 118) (.n 112) 5) ::
  .atom (.load (.n 119) (.n 112) 6) ::
  .atom (.load (.n 120) (.n 112) 7) ::
  .atom (.keccak [.n 83, .n 84, .n 86, .n 87, .n 89, .n 90, .n 92, .n 93, .n 77, .n 78, .n 79, .n 80, .n 81] [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126, .n 127, .n 128, .n 129, .n 130, .n 131, .n 132, .n 133] false false) ::
  .atom (.load (.n 134) (.n 55) 8) ::
  .atom (.copy (.n 135) (.n 134)) ::
  .atom (.const (.n 136) (word 0 1)) ::
  .atom (.load (.n 137) (.n 55) 9) ::
  .atom (.copy (.n 138) (.n 137)) ::
  .atom (.const (.n 139) (word 0 1)) ::
  [])

theorem vsReadsT_eq : (vsPre.drop 37).take 69 = vsReadsT := stmtsEqb_sound (by decide +kernel)


/-- **The seed**: its permutation writes the seed state's capacity. -/
theorem phSeed : PhSeed := by
  intro bytecode κ L C V σ rets R
  have h := R.slice vsSeedT_eq
  simp only [vsSeedT, Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨-, h25, h26, h27, h28, hk, -⟩ := h
  simp only [Atom.Holds, word_zero] at h25 h26 h27 h28
  exact ⟨(seed_cap hk h25 h26 h27 h28).symm, rfl, rfl⟩

/-- What `vsReadsT` gives: the announced words and the root's at `stream`, the absorbs, and the
words `g_power_of_word` reads (`x@8`, `x@1`) with its returns. -/
structure ReadsFacts (C : CallRel) (rd : Reader) (σ : Val) : Prop where
  words : ReadsAt rd (vsStream σ) (vsAnnounced σ)
  absorb : (vsF0 σ).absorbAll (vsAnnounced σ) dsObserve = vsF1 σ
  root : ReadsAt rd (vsStream σ * gen ^ 8)
    [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))]
  rootAbs : (((vsF1 σ).absorb (σ (.n (val% «verify_sub» "x@9"))) dsObserve).absorb
    (σ (.n (val% «verify_sub» "x@10"))) dsObserve) = vsF2 σ
  rateCall : C "g_power_of_word" [σ (.n (val% «verify_sub» "x@8"))] [σ (.n 94)]
  rateMul : σ (.n 94) = σ (.n (val% «verify_sub» "rate_sel")) * gen
  rateRc : LoadHolds rd (σ (.n (val% «verify_sub» "rate_sel"))) 0 (σ (.n 99)) ∧
    gen ^ 3 = σ (.n (val% «verify_sub» "rate_sel")) * σ (.n 98) ∧ LoadHolds rd (σ (.n 98)) 0 (σ (.n 100))
  memCall : C "g_power_of_word" [σ (.n (val% «verify_sub» "x@1"))] [σ (.n (val% «verify_sub» "g_log_mem"))]
  memRc : LoadHolds rd (σ (.n (val% «verify_sub» "g_log_mem"))) 0 (σ (.n 104)) ∧
    gen ^ 30 = σ (.n (val% «verify_sub» "g_log_mem")) * σ (.n 103) ∧ LoadHolds rd (σ (.n 103)) 0 (σ (.n 105))
  memMul : σ (.n (val% «verify_sub» "g_log_mem")) = σ (.n 108) * gen
  memRc2 : LoadHolds rd (σ (.n 108)) 0 (σ (.n 110)) ∧
    gen ^ 32 = σ (.n 108) * σ (.n 109) ∧ LoadHolds rd (σ (.n 109)) 0 (σ (.n 111))
  kb : σ (.n 113) = 1 ∧ σ (.n 114) = σ (.n (val% «verify_sub» "g_log_mem")) ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "kappa_base")))
      ((List.range 8).map fun i ↦ σ (.n (113 + i)))
  hlogs : ReadsAt rd (σ (.n (val% «verify_sub» "h_logs"))) ((List.range 6).map fun i ↦ σ (.n (115 + i)))
  rows : ∀ i < 6, LoadHolds rd (σ (.n (val% «verify_sub» "table_rows"))) i ((vsAnnounced σ).getD (i + 1) 0)

theorem gen_word (a : ℕ) (h : a < 64) : word (2 ^ a) 0 = gen ^ a := word_two_pow h

theorem readsFacts {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ vsReadsT True kret) : ReadsFacts C rd σ := by
  simp only [vsReadsT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, -⟩ := h
  have hc58 : σ (.n 58) = σ (.n 57) := a39
  have hc61 : σ (.n 61) = σ (.n 60) := a42
  have hc64 : σ (.n 64) = σ (.n 63) := a46
  have hc67 : σ (.n 67) = σ (.n 66) := a50
  have hc83 : σ (.n 83) = σ (.n 82) := a55
  have hc86 : σ (.n 86) = σ (.n 85) := a59
  have hc89 : σ (.n 89) = σ (.n 88) := a63
  have hc92 : σ (.n 92) = σ (.n 91) := a67
  have ht59 : σ (.n 59) = word 0 1 := a40
  have ht62 : σ (.n 62) = word 0 1 := a43
  have ht65 : σ (.n 65) = word 0 1 := a47
  have ht68 : σ (.n 68) = word 0 1 := a51
  have ht84 : σ (.n 84) = word 0 1 := a56
  have ht87 : σ (.n 87) = word 0 1 := a60
  have ht90 : σ (.n 90) = word 0 1 := a64
  have ht93 : σ (.n 93) = word 0 1 := a68
  have hcap1 := fs_perm_cap (s := ⟨[σ (.n 37), σ (.n 38), σ (.n 39), σ (.n 40), σ (.n 41)],
      [(σ (.n 57), dsObserve), (σ (.n 60), dsObserve), (σ (.n 63), dsObserve),
        (σ (.n 66), dsObserve)]⟩) a53 (by simp) (by
    simp only [List.map_cons, List.map_nil, hc58, hc61, hc64, hc67, ht59, ht62, ht65, ht68]; rfl)
  have hcap2 := fs_perm_cap (s := vsF1 σ) a99 (by simp [vsF1]) (by
    simp only [List.map_cons, List.map_nil, hc83, hc86, hc89, hc92, ht84, ht87, ht90, ht93]; rfl)
  refine ⟨?_, ?_, ?_, ?_, a69, ?_, ?_, a74, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [vsAnnounced, List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [a38, a41, a45, a49, a54, a58, a62, a66]
  · simp only [Fs.absorbAll, vsAnnounced, List.foldl_cons, List.foldl_nil, vsF0, vsF1, Fs.absorb,
      List.length_nil, List.length_cons, List.nil_append, List.cons_append, rateScalars, Nat.reduceAdd, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [← hcap1]
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact (loadHolds_mul_gen_pow _ _ _ _ _).mpr a100
    · exact (loadHolds_mul_gen_pow _ _ _ _ _).mpr a103
  · simp only [vsF2, Fs.absorb, List.length_cons, List.length_nil,
      rateScalars, List.nil_append, List.cons_append, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, show (vsF1 σ).pend.length = 4 from rfl]
    rw [← hcap2]
  · have e70 : σ (.n 95) = gen := by rw [a70, show (2 : ℕ) = 2 ^ 1 from rfl, gen_word 1 (by decide), pow_one]
    rw [a71, e70]
  · refine ⟨a73.1, ?_, a73.2.2⟩
    rw [← a73.2.1, a72, show (8 : ℕ) = 2 ^ 3 from rfl, gen_word 3 (by decide)]
  · refine ⟨a76.1, ?_, a76.2.2⟩
    rw [← a76.2.1, a75, show (1073741824 : ℕ) = 2 ^ 30 from rfl, gen_word 30 (by decide)]
  · have e78 : σ (.n 107) = gen := by rw [a78, show (2 : ℕ) = 2 ^ 1 from rfl, gen_word 1 (by decide), pow_one]
    rw [a79, e78]
  · refine ⟨a80.1, ?_, a80.2.2⟩
    rw [← a80.2.1, a77, show (4294967296 : ℕ) = 2 ^ 32 from rfl, gen_word 32 (by decide)]
  · refine ⟨by rw [a83, word_one], a84, ?_⟩
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    interval_cases k
    exacts [a91, a92, a93, a94, a95, a96, a97, a98]
  · intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    interval_cases k
    exacts [a85, a86, a87, a88, a89, a90]
  · intro i hi
    interval_cases i
    exacts [a44, a48, a52, a57, a61, a65]

/-- **The root**: its two words follow the sizes, absorbed. -/
theorem phRoot : PhRoot := fun _ _ _ _ _ _ _ R ↦
  ⟨(readsFacts (R.slice vsReadsT_eq)).root, (readsFacts (R.slice vsReadsT_eq)).rootAbs⟩

end
end LeanVM.Guest.B1.VerifySub
