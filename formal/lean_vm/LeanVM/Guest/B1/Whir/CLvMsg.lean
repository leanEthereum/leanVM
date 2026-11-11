/-
  LeanVM.Guest.B1.Whir.CLvMsg

  A level's message honestly on f128: the final lane by `opening_message` with its nonce, and a
  non-final level's next commitment, out-of-domain points and values and query nonce.
-/

module

public import LeanVM.Guest.B1.Whir.CBlk
public import LeanVM.Guest.B1.Whir.Commit

/-!
# A level's message, honestly

* `omRets cap ms nonce cur n`: what `opening_message` returns on the capacity `cap`, the words
  `ms`, the nonce and the cursor (its meaning's formula).
* `OsStep σ σ' st st'`: a block's state moved on: its invariants, its next free value, the
  agreement below the old one.
* `osFinalMsg_complete`: the final level's message (G:1568-1569) at its values.
* `osCommit_complete`: a non-final level's message, out-of-domain points and values and query
  nonce (G:1570-1592) at its values.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- `opening_message`'s returns. -/
def omRets (cap ms : List E) (nonce : Option E) (cur : E) (n : ℕ) : List E :=
  [cellsOfState (omState cap ms nonce) false 0, cellsOfState (omState cap ms nonce) false 1] ++
    capOf (omState cap ms nonce) ++ [cur * gen ^ n]

theorem omRets_length (cap ms : List E) (nonce : Option E) (cur : E) (n : ℕ) :
    (omRets cap ms nonce cur n).length = 8 := by
  simp [omRets, capOf]

/-- **A block's state moved on.** -/
structure OsStep (σ σ' : Val) (st st' : OsSt) : Prop where
  ok : st'.Ok σ'
  le : st.k ≤ st'.k
  agree : AgreeBelow st.k σ σ'

/-- The cursor, as a block at fixed values. -/
theorem osCurS_blkA {st : OsSt} (σ : Val) (hb : st.cb < st.k) (hco : st.co < u128Bound) :
    BlkA H σ st.k (osCurS st).2.2.k (osCurS st).1
      (fun σ' ↦ σ' (.n (osCurS st).2.1) = σ (.n st.cb) * gen ^ st.co) :=
  BlkA.ofF _ fun _ _ _ ↦ osCurS_blk σ hb hco

/-- **The final level's message, honestly** (G:1568-1569): `opening_message` with a nonce, its
returns `omRets` on the carried capacity, the lane `ms` and the nonce `nn`. -/
theorem osFinalMsg_complete {c : OsCfg} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ)
    (ms : List E) (nn : E)
    (hC : ∀ C rd, H C rd → C ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1")
      (st.fsv σ ++ [st.cur σ, σ (.n osFmsg)])
      (omRets (st.fsv σ) ms (some nn) (st.cur σ) (c.yrLen + lv.folds + 1))) :
    BlkA H σ st.k (osFinalMsg c lv st).2.k (osFinalMsg c lv st).1 (fun σ' ↦
      OsStep σ σ' st (osFinalMsg c lv st).2 ∧
      (osFinalMsg c lv st).2.F σ' = ⟨capOf (omState (st.fsv σ) ms (some nn)), []⟩ ∧
      σ' (.n (osFinalMsg c lv st).2.word0) = cellsOfState (omState (st.fsv σ) ms (some nn)) false 0 ∧
      σ' (.n (osFinalMsg c lv st).2.pow0) = cellsOfState (omState (st.fsv σ) ms (some nn)) false 1 ∧
      (osFinalMsg c lv st).2.cur σ' = st.cur σ * gen ^ (c.yrLen + lv.folds + 1) ∧
      (osFinalMsg c lv st).2.claim = st.claim ∧ (osFinalMsg c lv st).2.pad = st.pad) := by
  set cu := osCurS st with hcu
  set r := cu.2.2.k with hr
  set rets := omRets (st.fsv σ) ms (some nn) (st.cur σ) (c.yrLen + lv.folds + 1) with hrets
  have k1 : st.k ≤ r := osCurS_k st
  have pcu : cu.2.1 < r := osMat_ptr_lt _ _ _ hsf.below.cb
  have hA := osCurS_blkA (H := H) σ hsf.below.cb hsf.co
  have hall := BlkA.seq k1 (show r ≤ r + 8 by omega) hA (B := [.call
      ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1")
      ((st.fs ++ [cu.2.1, osFmsg]).map V.n) (osRun r 8)])
    (OutB := fun σ' ↦ ∀ j < 8, σ' (.n (r + j)) = rets.getD j 0) fun σ1 ha1 ho1 ↦ by
    refine call_blk rets (omRets_length _ _ _ _ _) (fun i hi ↦ ?_) fun C rd hH ↦ ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | rfl | rfl
      · have := hsf.below.fs i hi; omega
      · exact pcu
      · have := hsf.k; show 15 < r; omega
    · have e := ho1 C rd hH
      have hargs : (st.fs ++ [cu.2.1, osFmsg]).map (fun i ↦ σ1 (.n i)) =
          st.fsv σ ++ [st.cur σ, σ (.n osFmsg)] := by
        simp only [List.map_append, List.map_cons, List.map_nil, OsSt.fsv]
        congr 1
        · exact List.map_congr_left fun f hf ↦ ha1 f (hsf.below.fs f hf)
        · rw [e, ha1 osFmsg (by have := hsf.k; show 15 < st.k; omega)]; rfl
      rw [hargs]
      exact hC C rd hH
  refine BlkA.congr (BlkA.monoH hall.agree fun C rd hH σ' ha ⟨⟨_, hret⟩, hag⟩ ↦ ?_) rfl
  have e0 : ∀ j < 8, σ' (.n (r + j)) = rets.getD j 0 := hret
  have ek : (osFinalMsg c lv st).2.k = r + 8 := rfl
  have efs : (osFinalMsg c lv st).2.fs = [r + 2, r + 3, r + 4, r + 5, r + 6] := rfl
  have hok' := hok C rd hH
  refine ⟨⟨⟨⟨by rw [efs]; rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩, by rw [ek]; omega,
    hag⟩, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro f hf; rw [efs] at hf; rw [ek]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> omega
  · show r + 7 < r + 8; omega
  · show st.claim < r + 8; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b, d⟩ := hsf.below.mats m hm; rw [ek]; exact ⟨by omega, by omega, by omega⟩
  · show 0 < u128Bound; unfold u128Bound; positivity
  · intro p hp; have := hsf.padB p hp; rw [ek]; omega
  · rw [ek]; have := hsf.k; omega
  · exact matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ ha i hi
  · exact (hok'.agree ha).pad
  · simp only [OsSt.F, efs, List.map_cons, List.map_nil]
    rw [e0 2 (by omega), e0 3 (by omega), e0 4 (by omega), e0 5 (by omega), e0 6 (by omega)]
    simp [hrets, omRets, capOf]
  · rw [show (osFinalMsg c lv st).2.word0 = r + 0 from rfl, e0 0 (by omega)]; simp [hrets, omRets]
  · rw [show (osFinalMsg c lv st).2.pow0 = r + 1 from rfl, e0 1 (by omega)]; simp [hrets, omRets]
  · simp only [OsSt.cur, show (osFinalMsg c lv st).2.cb = r + 7 from rfl,
      show (osFinalMsg c lv st).2.co = 0 from rfl, pow_zero, mul_one]
    rw [e0 7 (by omega)]; simp [hrets, omRets, capOf, OsSt.cur]

/-- **A call returning nothing.** -/
theorem call0_blk {σ : Val} {k : ℕ} {f : String} {args : List ℕ} (hargs : ∀ i ∈ args, i < k)
    (hC : ∀ C rd, H C rd → C f (args.map fun i ↦ σ (.n i)) []) :
    BlkA H σ k k [.call f (args.map V.n) []] (fun σ' ↦ (args.map V.n).map σ' =
      args.map fun i ↦ σ (.n i)) := by
  refine ⟨fun _ ↦ 0, fun C rd hH σ' ha _ ↦ ?_⟩
  have e1 : (args.map V.n).map σ' = args.map fun i ↦ σ (.n i) := by
    simp only [List.map_map]
    exact List.map_congr_left fun i hi ↦ ha i (hargs i hi)
  refine ⟨?_, e1⟩
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, e1, List.map_nil]
  exact hC C rd hH


/-- The zero run's values. -/
def padVals : List E := [word 1 0, word 0 0, word 0 0, word 0 0, word 0 0]

/-- **The zero run**, allocated if it was not: its cells after the first zero. -/
theorem osPad_blk (σ : Val) (pad : Option ℕ) (k : ℕ) (hp : ∀ C rd, H C rd → PadOk σ pad)
    (hpb : ∀ p, pad = some p → p + 4 < k) :
    BlkA H σ k (osPad pad k).2.2 (osPad pad k).1 (fun σ' ↦ PadOk σ' (some (osPad pad k).2.1)) := by
  cases pad with
  | some q =>
    refine ⟨fun _ ↦ 0, fun C rd hH σ' ha _ ↦ ⟨allOk_nil, fun p hp ↦ ?_⟩⟩
    simp only [osPad, Option.some.injEq] at hp
    subst hp
    have hb := hpb q rfl
    obtain ⟨z1, z2, z3, z4⟩ := hp C rd hH q rfl
    rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  | none =>
    refine ⟨lstF k padVals, fun C rd hH σ' ha hr ↦ ?_⟩
    have v : ∀ j < 5, σ' (.n (k + j)) = padVals.getD j 0 := fun j hj ↦
      lstF_at hr (by simp [osPad, padVals]) j (by simp [padVals]; omega)
    have v0 := v 0 (by omega)
    have v1 := v 1 (by omega)
    have v2 := v 2 (by omega)
    have v3 := v 3 (by omega)
    have v4 := v 4 (by omega)
    simp only [padVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
      word_zero] at v0 v1 v2 v3 v4
    refine ⟨?_, fun p hp ↦ ?_⟩
    · simp only [osPad, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst, v0, v1, v2,
        v3, v4, word_zero]
    · simp only [osPad, Option.some.injEq] at hp
      subst hp
      exact ⟨v1, v2, v3, v4⟩

theorem osPad_next (pad : Option ℕ) (k : ℕ) : k ≤ (osPad pad k).2.2 := by
  cases pad <;> simp [osPad]

theorem osPad_ptr (pad : Option ℕ) (k : ℕ) (hpb : ∀ p, pad = some p → p + 4 < k) :
    (osPad pad k).2.1 + 4 < (osPad pad k).2.2 ∨ ((osPad pad k).2.1 + 4 < k) := by
  cases pad with
  | some q => right; exact hpb q rfl
  | none => left; simp [osPad]

end
end LeanVM.Guest.B1.Whir
