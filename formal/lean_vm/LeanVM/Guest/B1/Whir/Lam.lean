/-
  LeanVM.Guest.B1.Whir.Lam

  A non-final level's batching challenge `λ` (`osLam`), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The batching challenge (G:1632-1641)

`fs_grind_squeeze`: the batching nonce read at the cursor, absorbed with `DS_POW_NONCE` and
permuted (the zero run's cells for the rest of the rate), the grind checked on the permutation's
cell `1`, `λ` its cell `0` and `1/λ` constrained by `λ·μ = 1`. `osLam_sound`: that is
`Fs.grindSqueeze 14` on the nonce, which passes (`GrindOk`), and `λ ≠ 0`. `PadOk`: the zero run's
cells are zero, once allocated.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The zero run's cells past its first are zero, once it is allocated. -/
def PadOk (σ : Val) (pad : Option ℕ) : Prop :=
  ∀ p, pad = some p → σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧
    σ (.n (p + 4)) = 0

/-- The zero run, allocated if it was not: its cells are zero. -/
theorem osPad_ok {pad : Option ℕ} {k : ℕ} (hp : PadOk σ pad) (hok : AllOk C rd σ (osPad pad k).1) :
    PadOk σ (some (osPad pad k).2.1) := by
  intro p hpe
  simp only [Option.some.injEq] at hpe
  subst hpe
  cases pad with
  | some q => exact hp q rfl
  | none =>
    simp only [osPad, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst] at hok ⊢
    obtain ⟨-, h1, h2, h3, h4⟩ := hok
    exact ⟨h1.trans word_zero, h2.trans word_zero, h3.trans word_zero, h4.trans word_zero⟩

/-- What a non-final level's batching challenge leaves: the nonce `n` read at the cursor, the
grind passing, `λ` and the sponge `Fs.grindSqueeze 14 n` of the carried one, `λ·μ = 1`. -/
structure LamOut (rd : Reader) (σ : Val) (st st' : OsSt) (n : E) : Prop where
  reads : LoadHolds rd (st.cur σ) 0 n
  ok : (st.F σ).GrindOk batchGrind n
  lam : σ (.n st'.lam) = ((st.F σ).grindSqueeze batchGrind n).1
  F : st'.F σ = ((st.F σ).grindSqueeze batchGrind n).2
  inv : σ (.n st'.lam) * σ (.n st'.lamInv) = 1
  cur : st'.cur σ = st.cur σ * gen
  fs : st'.fs.length = 5
  mats : st'.mats = st.mats
  pad : PadOk σ st'.pad
  co : st'.co = st.co + 1
  claim : st'.claim = st.claim

/-- **A non-final level's batching challenge, soundly** (G:1632-1641). -/
theorem osLam_sound {st : OsSt}
    (hgr : ∀ w, C ("grind_check__L" ++ natStr batchGrind) [w, σ (.n osTabs)] [] →
      (w.limb 0).lane.toNat % 2 ^ batchGrind = 0)
    (hfs : st.fs.length = 5) (hpad : PadOk σ st.pad) (hok : AllOk C rd σ (osLam st).1) :
    ∃ n, LamOut rd σ st (osLam st).2 n := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  unfold osLam at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨hn, hpd⟩, hrest⟩ := hok
  have hP := osPad_ok hpad hpd
  set p := (osPad st.pad (st.k + 3)).2.1 with hp
  set j := (osPad st.pad (st.k + 3)).2.2 with hj
  obtain ⟨z1, z2, z3, z4⟩ := hP p rfl
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, stmtOk_call, holds_load, holds_copy,
    holds_const, holds_mul, osLd, osCp, osCst, osMul, osKeccak, List.map_cons, List.map_nil] at hn hrest
  obtain ⟨ln, c1, c2⟩ := hn
  obtain ⟨hK, hg, cl, one, hinv⟩ := hrest
  rw [hf] at hK
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], []⟩ := by
    simp [OsSt.F, hf]
  set n := σ (.n st.k)
  have hS : (st.F σ).nonceState n =
      (⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)], [(n, dsPowNonce)]⟩ : Fs).perm := by
    rw [hF]; simp [Fs.nonceState, Fs.absorb, rateScalars]
  have hout := keccakA_fs (s := (⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
      [(n, dsPowNonce)]⟩ : Fs)) hK (by simp) (by
    simp [pendCells, Keccak.scalarCells, c1, c2, z1, z2, z3, z4, dsPowNonce, word, n]
    exact rfl)
  rw [← hS] at hout
  have o : ∀ i : Fin 13, σ (.n (j + i.val)) = cellsOfState ((st.F σ).nonceState n) false i :=
    outCellK hout
  have hb : batchGrind ≠ 0 := by decide
  obtain ⟨gok, hlam, hsp⟩ := grindSqueeze_cells hb n _ _ (o 0) (o 1) (hgr _ hg)
  refine ⟨n, ⟨?_, gok, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl⟩⟩
  · simpa [OsSt.cur, loadHolds_mul_gen_pow] using ln
  · show σ (.n (j + 13)) = _
    rw [cl, hlam]
    simp
  · rw [hsp]
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
  · simp only [OsSt.cur, pow_succ, mul_assoc]
  · intro q hq
    simp only [Option.some.injEq] at hq
    subst hq
    exact ⟨z1, z2, z3, z4⟩

end
end LeanVM.Guest.B1.Whir
