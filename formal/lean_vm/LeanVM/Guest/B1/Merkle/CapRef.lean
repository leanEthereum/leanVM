/-
  LeanVM.Guest.B1.Merkle.CapRef

  `verify_merkle_cap`'s reference function, at every cap depth, and its meaning.
-/

module

public import LeanVM.Guest.Ref.Link
public import LeanVM.Guest.B1.Merkle.Meaning

/-!
# `verify_merkle_cap`, from its source

`capRef depth` is `verify_merkle_cap(cap, flags, depth)` of `guests/lean_ethereum.py` read line
by line (`LeanVM.Guest.Ref.Lang`): the `Const` depth a Lean argument, each `unroll` an `unroll`,
each `if const` an `if`, the frame run `runs` and the flags read the names of `CapName`. The
size of `runs` (the `StackBuf` chosen per depth) is not read: a cell is a name, and a run's size
constrains nothing.
`capRef_sem` is its meaning at every depth; `B1/Merkle/CapLinks.lean` ties the deployed
specializations to it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref

@[expose] public section

/-- The names of `verify_merkle_cap`. -/
inductive CapName where
  | cap
  | flags
  /-- Cell `i` of the frame run `runs`. -/
  | runs (i : ℕ)
  /-- The flag read at `node`. -/
  | flag (node : ℕ)
  /-- `root_i`, read at depth zero. -/
  | root (i : ℕ)
  deriving DecidableEq

instance : Coded CapName where
  code
    | .cap => 0
    | .flags => 1
    | .runs i => 3 * i + 2
    | .flag node => 3 * node + 3
    | .root i => 3 * i + 4

/-- `verify_merkle_cap(cap, flags, depth)`. -/
def capRef (depth : ℕ) : Func CapName :=
  let nLeaves := 2 ^ depth
  let cap : Tm CapName := .v .cap
  let flags : Tm CapName := .v .flags
  let runs (i : ℕ) : Tm CapName := .v (.runs i)
  let keccak (l r out : ℕ) : Cmd CapName :=
    .hash2 (runs l) (runs (l + 1)) (runs r) (runs (r + 1)) (runs out) (runs (out + 1))
  { params := [.cap, .flags]
    body :=
      if depth ≠ 0 then
        (unroll 1 (2 * nLeaves) fun node ↦
          let at_ := 2 * (node - 1)
          [.load (runs at_) cap (2 * node), .load (runs (at_ + 1)) cap (2 * node + 1)]) ++
        unroll 1 nLeaves fun node ↦
          let left := 2 * (2 * node - 1)
          let right := left + 2
          let at_ := 2 * (node - 1)
          if node = 1 then [keccak left right at_]
          else
            [.load (.v (.flag node)) flags node,
              .ifNz (.v (.flag node))
                (if 2 * node / nLeaves = 0 then
                  [.load (.const (word 0 0)) flags (2 * node),
                    .load (.const (word 0 0)) flags (2 * node + 1)]
                else [])
                [keccak left right at_]]
      else [.load (.v (.root 0)) cap 2, .load (.v (.root 1)) cap 3]
    rets := if depth ≠ 0 then [runs 0, runs 1] else [.v (.root 0), .v (.root 1)] }

/-- The names' words, from the cap's cells and the flags. -/
def capVal (cap flags : E) (cell fl : ℕ → E) : CapName → E
  | .cap => cap
  | .flags => flags
  | .runs i | .root i => cell (i + 2)
  | .flag k => fl k

/-- **`verify_merkle_cap`'s reference function is its meaning**, at every depth. -/
theorem capRef_sem (D : ℕ) (rd : Reader) (args rets : List E) :
    (capRef D).Sem rd args rets ↔ MeaningVerifyMerkleCap D rd args rets := by
  have h4 : 2 ^ (D + 2) = 4 * 2 ^ D := by rw [pow_add]; ring
  have hpos : 0 < 2 ^ D := Nat.two_pow_pos D
  constructor
  · rintro ⟨ρ, rfl, hb, rfl⟩
    show MeaningVerifyMerkleCap D rd [ρ .cap, ρ .flags] _
    rw [MeaningVerifyMerkleCap]
    by_cases hD : D = 0
    · subst hD
      obtain ⟨h2, h3, -⟩ := hb
      refine ⟨fun k ↦ ρ (.root (k - 2)), fun _ ↦ 0, fun k _ hk ↦ ?_, fun k _ hk ↦ by omega,
        fun k _ hk ↦ by omega, fun k _ hk ↦ by omega, rfl⟩
      obtain rfl | rfl : k = 2 ∨ k = 3 := by omega
      exacts [h2, h3]
    · simp only [capRef, ne_eq, hD, not_false_eq_true, ↓reduceIte, Cmd.satList_append,
        Cmd.satList_unroll, apply_ite (Cmd.SatList rd ρ), Cmd.satList_cons, Cmd.Sat, Tm.eval,
        Cmd.satList_nil, and_true, Nat.div_eq_zero_iff_lt hpos] at hb
      obtain ⟨hA, hB⟩ := hb
      refine ⟨fun k ↦ ρ (.runs (k - 2)), fun k ↦ ρ (.flag k), fun k h2 hk ↦ ?_, fun k h2 hk ↦ ?_,
        fun k h1 hk hf ↦ ?_, fun k h2 hk hf ↦ ?_, by simp [capRef, hD, Tm.eval]⟩
      · obtain ⟨n, rfl | rfl⟩ : ∃ n, k = 2 * n ∨ k = 2 * n + 1 := ⟨k / 2, by omega⟩
        · have := (hA n (by omega) (by omega)).1
          rwa [show 2 * (n - 1) = 2 * n - 2 by omega] at this
        · have := (hA n (by omega) (by omega)).2
          rwa [show 2 * (n - 1) + 1 = 2 * n + 1 - 2 by omega] at this
      · have := hB k (by omega) hk
        rw [ite_neg' (by omega)] at this
        exact ⟨this.1, this.2.1⟩
      · have := hB k h1 hk
        by_cases e : k = 1
        · rw [ite_pos' e] at this
          convert this using 3 <;> omega
        · rw [ite_neg' e] at this
          convert this.2.2.2 (hf.resolve_left e) using 3 <;> omega
      · have := hB k (by omega) (by omega)
        rw [ite_neg' (by omega), ite_pos' hk, word_zero] at this
        exact this.2.2.1 hf
  · intro hm
    obtain ⟨cap, flags, rfl⟩ : ∃ cap flags, args = [cap, flags] := by
      match args, hm with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    rw [MeaningVerifyMerkleCap] at hm
    obtain ⟨cell, fl, hcell, hfl, hhash, hpin, rfl⟩ := hm
    by_cases hD : D = 0
    · subst hD
      exact ⟨capVal cap flags cell fl, rfl,
        ⟨hcell 2 le_rfl (by norm_num), hcell 3 (by norm_num) (by norm_num), trivial⟩, rfl⟩
    · refine ⟨capVal cap flags cell fl, rfl, ?_, by simp [capRef, hD, Tm.eval, capVal]⟩
      simp only [capRef, ne_eq, hD, not_false_eq_true, ↓reduceIte, Cmd.satList_append,
        Cmd.satList_unroll, apply_ite (Cmd.SatList rd _), Cmd.satList_cons, Cmd.Sat, Tm.eval,
        Cmd.satList_nil, and_true, Nat.div_eq_zero_iff_lt hpos, capVal]
      refine ⟨fun n h1 h2 ↦ ⟨?_, ?_⟩, fun n h1 h2 ↦ ?_⟩
      · rw [show 2 * (n - 1) + 2 = 2 * n by omega]
        exact hcell _ (by omega) (by omega)
      · rw [show 2 * (n - 1) + 1 + 2 = 2 * n + 1 by omega]
        exact hcell _ (by omega) (by omega)
      · by_cases e : n = 1
        · rw [ite_pos' e]
          convert hhash n h1 h2 (.inl e) using 2 <;> omega
        · rw [ite_neg' e]
          refine ⟨(hfl n (by omega) h2).1, (hfl n (by omega) h2).2, fun h0 ↦ ?_, fun hne ↦ ?_⟩
          · split_ifs with h2n
            simpa only [word_zero] using hpin n (by omega) h2n h0
          · convert hhash n h1 h2 (.inr hne) using 2 <;> omega

end
end LeanVM.Guest.B1
