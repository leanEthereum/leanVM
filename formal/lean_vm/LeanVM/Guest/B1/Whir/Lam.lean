/-
  LeanVM.Guest.B1.Whir.Lam

  A non-final level's batching challenge `λ` (`osLam`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The batching challenge (G:1620-1630)

`squeeze`: the query message's last squeeze, a permutation of the carried capacity (the zero
run's cells for the rate), `λ` its cell `0` and `1/λ` constrained by `λ·μ = 1`. `osLam_sound`:
that is `Fs.squeeze`, and `λ ≠ 0`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What a non-final level's batching challenge leaves: `λ` and the sponge `Fs.squeeze` of the
carried one, `λ·μ = 1`. -/
structure LamOut (σ : Val) (st st' : OsSt) : Prop where
  lam : σ (.n st'.lam) = (st.F σ).squeeze.1
  F : st'.F σ = (st.F σ).squeeze.2
  inv : σ (.n st'.lam) * σ (.n st'.lamInv) = 1
  cur : st'.cur σ = st.cur σ
  fs : st'.fs.length = 5
  mats : st'.mats = st.mats
  pad : PadOk σ st'.pad
  co : st'.co = st.co
  claim : st'.claim = st.claim

/-- **A non-final level's batching challenge, soundly** (G:1620-1630). -/
theorem osLam_sound {st : OsSt} (hfs : st.fs.length = 5)
    (hpad : PadOk σ st.pad) (hok : AllOk C rd σ (osLam st).1) : LamOut σ st (osLam st).2 := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osLam at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨hpd, hrest⟩ := hok
  have hP := osPad_ok hpad hpd
  set p := (osPad st.pad st.k).2.1 with hp
  set j := (osPad st.pad st.k).2.2 with hj
  obtain ⟨z1, z2, z3, z4⟩ := hP p rfl
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy, holds_const, holds_mul,
    osCp, osCst, osMul, osKeccak] at hrest
  obtain ⟨hK, cl, one, hinv⟩ := hrest
  rw [hf] at hK
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ := by
    simp [OsSt.F, hf]
  have hout := keccakA_fs (s := (⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ : Fs))
    hK (by simp) (by simp [pendCells, z1, z2, z3, z4])
  rw [← hF] at hout
  have o : ∀ i : Fin 13, σ (.n (j + i.val)) = cellsOfState (st.F σ).perm false i := outCellK hout
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
  · show σ (.n (j + 13)) = _
    rw [cl, Fs.squeeze, Keccak.challengeOf_cells]
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
  · show σ (.n (j + 13)) * σ (.n (j + 15)) = 1
    rw [mul_comm, ← hinv, one]
    exact word_one
  · intro q hq
    simp only [Option.some.injEq] at hq
    subst hq
    exact ⟨z1, z2, z3, z4⟩

end
end LeanVM.Guest.B1.Whir
