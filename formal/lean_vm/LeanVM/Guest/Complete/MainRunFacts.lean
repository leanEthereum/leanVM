/-
  LeanVM.Guest.Complete.MainRunFacts

  Facts `main`'s windows ask: its guards, its own DA digest.
-/

module

public import LeanVM.Guest.Complete.MainEval
public import LeanVM.Guest.Complete.MainSeg
public import LeanVM.Guest.Complete.MainCalleesA
public import LeanVM.Guest.Complete.DaPad
public import LeanVM.Guest.B1.Da.VerifyDefs
import LeanVM.Guest.B1.Main.Basic

/-!
# What `main`'s windows ask, proved

* **Guards.** `guard_eq_zero_iff`: a `callIf` guard `1 + g^n` (`n < 2^34`) is zero exactly when `n = 0`, so
  a loop over `n` iterations is entered exactly when `n ≠ 0`.
* **The guards' values.** `mVal_meta`: the counts `.n 0 ..< .n 8` are the oracle's words; `mVal_guards`: the
  five guards are `1 + w j` for the count `j` each loop runs over; `mVal_guard_zero_iff`.
* **The own DA digest.** `mDa_keccak`: on the direct DA check's arm, `main`'s `KECCAK` outputs
  (`.n 394`, `.n 395`) on its forward valuation are the halves of Keccak-256 of the cells
  `[root_0, root_1, z, 0]`; `da_cells_digest`: those cells' digest is `daClaimDigest`; `mDa_own`: with
  the claim's root halves and challenge returned by `da_verify`, the outputs are `ownDaCells`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Guards -/

/-- **A `callIf` guard** `1 + g^n` is zero exactly when `n = 0`. -/
theorem guard_eq_zero_iff {n : ℕ} (hn : n < 2 ^ 34) : word 1 0 + gen ^ n = 0 ↔ n = 0 :=
  not_iff_not.mp (decide_eq_decide.mp (one_add_gen_pow_ne hn))

/-! ## The own DA digest -/

theorem atom_mem_of_atomsOf {a : Atom} : ∀ {ss : List Stmt}, a ∈ atomsOf ss → Stmt.atom a ∈ ss
  | [], h => by simp [atomsOf] at h
  | .atom b :: ss, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)
  | .ite _ _ _ :: ss, h => List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)
  | .match_ _ _ :: ss, h => List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)
  | .call _ _ _ :: ss, h => List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)
  | .callIf _ _ _ :: ss, h => List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)
  | .dispatch _ _ _ _ :: ss, h => List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)
  | .ret _ :: ss, h => List.mem_cons_of_mem _ (atom_mem_of_atomsOf h)

/-- The DA arm's `KECCAK`: its constants and its permutation, statements `1 ..< 8` of `mDa`. -/
noncomputable def mDaK : List Atom := atomsOf ((mDa.drop 1).take 7)

set_option maxRecDepth 200000 in
theorem mDaK_ok : Da.pairHashVOk mDaK (.n 385) (.n 386) (.n 387) (.n 389) (.n 394) (.n 395) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mDaK_plain : mDaK.all (plainOkT []) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem mDaK_389 : Atom.const (.n 389) (word 0 0) ∈ mDaK := by decide +kernel

theorem mDa_389 : Stmt.atom (.const (.n 389) (word 0 0)) ∈ mDa :=
  List.mem_of_mem_drop (List.mem_of_mem_take (atom_mem_of_atomsOf mDaK_389))

theorem over_nil (σ : Val) (rd : Reader) : over [] σ rd = σ := funext fun _ => over_eq rfl

/-- **The direct DA check's `KECCAK`** on `main`'s forward valuation: its outputs are the halves of
Keccak-256 of `[root_0, root_1, z, 0]`. -/
theorem mDa_keccak {rd : Reader} {w : ℕ → E} (h : mVal rd w (.n 384) = 0) :
    (mVal rd w (.n 394), mVal rd w (.n 395)) = digestHalves (keccak256 (cellsBytes
      [mVal rd w (.n 385), mVal rd w (.n 386), mVal rd w (.n 387), 0])) := by
  have h389 : mVal rd w (.n 389) = 0 := by
    have := mVal_goodDa h _ mDa_389
    exact this.trans word_zero
  rw [← h389]
  refine Da.pairHashV_sound (rd := rd) mDaK_ok fun x hx => ?_
  have hm : Stmt.atom x ∈ mDa :=
    List.mem_of_mem_drop (List.mem_of_mem_take (atom_mem_of_atomsOf hx))
  have hx' := holdsT_plain (rd := rd) (List.all_eq_true.mp mDaK_plain x hx) (mVal_goodDa h _ hm)
  rwa [over_nil] at hx'

/-- **The DA claim's digest from its cells**: the root's halves, the challenge and a zero word. -/
theorem da_cells_digest (c : DaClaim) :
    keccak256 (cellsBytes [(digestHalves c.daRoot).1, (digestHalves c.daRoot).2, c.membershipChallenge, 0]) =
      daClaimDigest c := by
  unfold daClaimDigest
  rw [show [(digestHalves c.daRoot).1, (digestHalves c.daRoot).2, c.membershipChallenge, 0] =
      [(digestHalves c.daRoot).1, (digestHalves c.daRoot).2] ++ [c.membershipChallenge, 0] from rfl,
    cellsBytes, List.flatMap_append, ← cellsBytes, ← digestBytes_eq_cells]
  have e0 : cellBytes (0 : E) = List.replicate 16 0 := by decide +kernel
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, e0, List.append_assoc]
  rfl

/-- **The own DA digest's cells** on the direct DA check's arm: with `da_verify`'s returns the claim's
root halves and challenge, the `KECCAK`'s outputs are `ownDaCells`. -/
theorem mDa_own {rd : Reader} {o : ℕ → E} {w : NodeWitness} {c : DaClaim}
    (hw : ∃ m, w.daMatrix = some (c, m)) (h : mVal rd o (.n 384) = 0)
    (h5 : mVal rd o (.n 385) = (digestHalves c.daRoot).1) (h6 : mVal rd o (.n 386) = (digestHalves c.daRoot).2)
    (h7 : mVal rd o (.n 387) = c.membershipChallenge) :
    [mVal rd o (.n 394), mVal rd o (.n 395)] = ownDaCells w := by
  have hk := mDa_keccak (w := o) h
  rw [h5, h6, h7, da_cells_digest] at hk
  obtain ⟨m, hm⟩ := hw
  simp only [ownDaCells, hm, Prover.digestCells, ← hk]

/-! ## The counts and the guards on the forward valuation -/

theorem mPre_good {rd : Reader} {w : ℕ → E} {a : Atom} (h : a ∈ atomsOf mPre) :
    Good rd (storesOf 0 mPre) w (mVal rd w) a :=
  mVal_goodPre (.atom a) (atom_mem_of_atomsOf h)

theorem mMid_good {rd : Reader} {w : ℕ → E} {a : Atom} (h : a ∈ atomsOf mMid) :
    Good rd (storesOf 398 mMid) w (mVal rd w) a :=
  mVal_goodMid (.atom a) (atom_mem_of_atomsOf h)

set_option maxRecDepth 200000 in
theorem mPre_meta : Atom.hint (.witness "meta" (.stack ((List.range 8).map V.n))) ∈ atomsOf mPre := by
  decide +kernel

/-- **`main`'s counts** (`meta`, `.n 0 ..< .n 8`) are the oracle's words. -/
theorem mVal_meta {rd : Reader} {w : ℕ → E} {i : ℕ} (hi : i < 8) : mVal rd w (.n i) = w i :=
  mPre_good (rd := rd) (w := w) mPre_meta (.n i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

set_option maxRecDepth 200000 in
theorem mGuards_mem :
    (Atom.const (.n 58) (word 1 0) ∈ atomsOf mPre ∧ Atom.add (.n 59) (.n 58) (.n 1) ∈ atomsOf mPre) ∧
    (Atom.const (.n 61) (word 1 0) ∈ atomsOf mPre ∧ Atom.add (.n 62) (.n 61) (.n 4) ∈ atomsOf mPre) ∧
    (Atom.const (.n 374) (word 1 0) ∈ atomsOf mPre ∧ Atom.add (.n 375) (.n 374) (.n 2) ∈ atomsOf mPre) ∧
    (Atom.const (.n 377) (word 1 0) ∈ atomsOf mPre ∧ Atom.add (.n 378) (.n 377) (.n 5) ∈ atomsOf mPre) ∧
    (Atom.const (.n 405) (word 1 0) ∈ atomsOf mMid ∧ Atom.add (.n 406) (.n 405) (.n 6) ∈ atomsOf mMid) := by
  decide +kernel

theorem guard_of_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a c b : V}
    (h1 : Good rd S w σ (.const a (word 1 0))) (h2 : Good rd S w σ (.add c a b)) : σ c = word 1 0 + σ b := by
  have e2 : σ c = σ a + σ b := h2
  rw [e2, show σ a = word 1 0 from h1]

/-- **`main`'s five guards** on its forward valuation: `1 + g^n`, `n` the count the loop runs over (the
leanXMSS and leanSPHINCS duplicates, the raw leanXMSS and leanSPHINCS signatures, the children), when the
oracle's counts are `g^n`. -/
theorem mVal_guards {rd : Reader} {w : ℕ → E} :
    mVal rd w (.n 59) = word 1 0 + w 1 ∧ mVal rd w (.n 62) = word 1 0 + w 4 ∧
      mVal rd w (.n 375) = word 1 0 + w 2 ∧ mVal rd w (.n 378) = word 1 0 + w 5 ∧
      mVal rd w (.n 406) = word 1 0 + w 6 := by
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := mGuards_mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [guard_of_good (mPre_good (rd := rd) (w := w) a1) (mPre_good b1), mVal_meta (by norm_num)]
  · rw [guard_of_good (mPre_good (rd := rd) (w := w) a2) (mPre_good b2), mVal_meta (by norm_num)]
  · rw [guard_of_good (mPre_good (rd := rd) (w := w) a3) (mPre_good b3), mVal_meta (by norm_num)]
  · rw [guard_of_good (mPre_good (rd := rd) (w := w) a4) (mPre_good b4), mVal_meta (by norm_num)]
  · rw [guard_of_good (mMid_good (rd := rd) (w := w) a5) (mMid_good b5), mVal_meta (by norm_num)]

/-- **A guard on the honest counts** is zero exactly when its count is. -/
theorem mVal_guard_zero_iff {rd : Reader} {w : ℕ → E} {c : V} {j n : ℕ} (hn : n < 2 ^ 34)
    (hc : mVal rd w c = word 1 0 + w j) (hw : w j = gen ^ n) : mVal rd w c = 0 ↔ n = 0 := by
  rw [hc, hw]; exact guard_eq_zero_iff hn

end
end LeanVM.Guest.Complete
