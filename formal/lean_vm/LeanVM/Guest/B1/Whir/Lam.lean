/-
  LeanVM.Guest.B1.Whir.Lam

  A non-final level's batching challenge `λ` (`osLam`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes
public import LeanVM.Guest.B1.Whir.SlowSpec

/-!
# The batching challenge

`squeeze`: the query message's last squeeze, a permutation of the carried capacity (the zero
run's cells for the rate), `λ` its cell `0` and `μ` constrained by `(λ + is_zero(λ))·μ = 1`.
`osLam_sound`: that is `Fs.squeeze`, and `λ·μ = 1` where `λ ≠ 0`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What a non-final level's batching challenge leaves: `λ` and the sponge `Fs.squeeze` of the
carried one, `λ·μ = 1` where `λ ≠ 0`. -/
structure LamOut (σ : Val) (st st' : OsSt) : Prop where
  lam : σ (.n st'.lam) = (st.F σ).squeeze.1
  F : st'.F σ = (st.F σ).squeeze.2
  inv : σ (.n st'.lam) ≠ 0 → σ (.n st'.lam) * σ (.n st'.lamInv) = 1
  cur : st'.cur σ = st.cur σ
  fs : st'.fs.length = 5
  mats : st'.mats = st.mats
  pad : PadOk σ st'.pad
  co : st'.co = st.co
  claim : st'.claim = st.claim

/-- **A non-final level's batching challenge, soundly**. -/
theorem osLam_sound {st : OsSt} (hfs : st.fs.length = 5)
    (hiz : ∀ a r, C "is_zero" a r → MeaningIsZero a r)
    (hpad : PadOk σ st.pad) (hok : AllOk C rd σ (osLam st).1) : LamOut σ st (osLam st).2 := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osLam at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨hcp, hpd⟩, hrest⟩ := hok
  rw [hf] at hcp
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons, allOk_nil,
    and_true, stmtOk_atom, holds_copy, osCp, Nat.zero_add] at hcp
  obtain ⟨c0, c1, c2, c3, c4⟩ := hcp
  have hP := osPad_ok hpad hpd
  set p := (osPad st.pad (st.k + 5)).2.1 with hp
  set j := (osPad st.pad (st.k + 5)).2.2 with hj
  obtain ⟨z1, z2, z3, z4⟩ := hP p rfl
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, stmtOk_call, holds_const, holds_mul,
    holds_add, osCst, osMul, osAdd, osKeccak] at hrest
  obtain ⟨hK, one, hz, hadd, hinv⟩ := hrest
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ := by
    simp [OsSt.F, hf]
  have hout := keccakA_fs (s := (⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ : Fs))
    hK (by simp) (by simp [pendCells, z1, z2, z3, z4]; exact ⟨by simpa using c0, c1, c2, c3, c4⟩)
  rw [← hF] at hout
  have o : ∀ i : Fin 13, σ (.n (j + i.val)) = cellsOfState (st.F σ).perm false i := outCellK hout
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
  · show σ (.n j) = _
    rw [Fs.squeeze, Keccak.challengeOf_cells]
    simpa using o 0
  · rw [Fs.squeeze]
    simp only [OsSt.F, capOf, List.map_cons, List.map_nil]
    have e8 : σ (.n (j + 8)) = _ := o 8
    have e9 : σ (.n (j + 9)) = _ := o 9
    have e10 : σ (.n (j + 10)) = _ := o 10
    have e11 : σ (.n (j + 11)) = _ := o 11
    have e12 : σ (.n (j + 12)) = _ := o 12
    rw [e8, e9, e10, e11, e12]
    rfl
  · show σ (.n j) ≠ 0 → σ (.n j) * σ (.n (j + 16)) = 1
    intro h0
    have hz' := zeroOf_of_meaning (hiz _ _ hz)
    simp only [zeroOf, h0, ↓reduceIte] at hz'
    rw [hz', add_zero] at hadd
    rw [mul_comm, ← hadd, ← hinv, one]
    exact word_one
  · intro q hq
    simp only [Option.some.injEq] at hq
    subst hq
    exact ⟨z1, z2, z3, z4⟩

end
end LeanVM.Guest.B1.Whir
