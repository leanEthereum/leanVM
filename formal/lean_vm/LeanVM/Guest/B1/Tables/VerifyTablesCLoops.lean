/-
  LeanVM.Guest.B1.Tables.VerifyTablesCLoops

  `verify_tables`' selector loops backward: from the honest words in memory, each loop's relation.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSel
public import LeanVM.Guest.B1.Tables.VerifyTablesFront
public import LeanVM.Guest.B1.Main.LoopsC

/-!
# The selector loops, backward

`sel_complete`: a selector loop (`selPre`, any of the 65) holds from `g^0` to `g^m` once each
iteration's words hold (`SelBody`); likewise the index loops (`idx_complete`), the table sumcheck's
equality prefix (`loop80_complete`) and its rounds (`loop79_complete`, `ZcRound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem sel_back {self : String} (hok : selOk self = true) {N sb ec zh go sq ka : E} (d j : ℕ)
    (hK : IsInK (gen ^ j * gen + N)) (hB : SelBody rd sb ec zh go sq ka (gen ^ j))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.relN rd d self [gen ^ j * gen, N, sb, ec, zh, go, sq, ka] []) :
    coreProgram.relN rd (d + 1) self [gen ^ j, N, sb, ec, zh, go, sq, ka] [] := by
  unfold selOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hpar, hbody⟩ := hok
    obtain ⟨bit, e, z, o, s, l9, hbb, l13, l17, l19, l22, l26, l31⟩ := hB
    set x := gen ^ j
    rw [relN_succ_iff hf]
    refine ⟨setl (Val.ofArgs [x, N, sb, ec, zh, go, sq, ka]) 8 [sb * x, bit, bit * bit, sb * x, ec * x, e,
      word 1 0 0, word 1 0 0 + bit, zh * x, z, word 1 0 0 + bit + z, e * (word 1 0 0 + bit + z), ec * x,
      go * x, o, word 1 0 0, ka * x, sq * (ka * x), s, word 1 0 0, s + word 1 0 0, bit * (s + word 1 0 0),
      word 1 0 0 + bit * (s + word 1 0 0), o * (word 1 0 0 + bit * (s + word 1 0 0)), go * x, word 2 0 0,
      x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by
        simp only [hpar, List.map_cons, List.map_nil]; b1_look, ?_⟩
    rw [stmtsEqb_sound hbody]
    simp only [selPre, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil]
    b1_look
    simp only [true_and, and_true, word_one, word_gen]
    rw [hbb]
    exact ⟨l9, l9, l13, l17, l19, l22, l26, l31, hK, hnext⟩
  · exact absurd hok (by simp)

/-- **A selector loop** runs its `m` iterations from their honest words. -/
theorem sel_complete {self : String} (hok : selOk self = true) {N sb ec zh go sq ka : E} {m : ℕ}
    (hm0 : 0 < m) (hN : N = gen ^ m) (hB : ∀ j < m, SelBody rd sb ec zh go sq ka (gen ^ j)) :
    coreProgram.Rel rd self [1, N, sb, ec, zh, go, sq, ka] [] :=
  Main.loop_complete hm0 hN hB fun d j hj hK hnext => sel_back hok d j hK hj hnext

/-- An index loop's iteration at `x`. -/
def IdxBody (rd : Reader) (ch z fac x : E) : Prop :=
  ∃ c zt ft, LoadHolds rd (ch * x) 0 c ∧ LoadHolds rd (z * x) 0 zt ∧
    LoadHolds rd (fac * x) 0 ft ∧ LoadHolds rd (ch * x) 1 (c * (1 + zt * ft))

theorem idx_back {self : String} (hok : idxOk self = true) {N ch z fac : E} (d j : ℕ)
    (hK : IsInK (gen ^ j * gen + N)) (hB : IdxBody rd ch z fac (gen ^ j))
    (hnext : gen ^ j * gen + N ≠ 0 → coreProgram.relN rd d self [gen ^ j * gen, N, ch, z, fac] []) :
    coreProgram.relN rd (d + 1) self [gen ^ j, N, ch, z, fac] [] := by
  unfold idxOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hpar, hbody⟩ := hok
    obtain ⟨c, zt, ft, l6, l9, l11, l14⟩ := hB
    set x := gen ^ j
    rw [relN_succ_iff hf]
    refine ⟨setl (Val.ofArgs [x, N, ch, z, fac]) 5 [ch * x, c, word 1 0 0, z * x, zt, fac * x, ft,
      zt * ft, word 1 0 0 + zt * ft, c * (word 1 0 0 + zt * ft), ch * x, word 2 0 0, x * word 2 0 0,
      x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by
        simp only [hpar, List.map_cons, List.map_nil]; b1_look, ?_⟩
    rw [stmtsEqb_sound hbody]
    simp only [idxPre, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil]
    b1_look
    simp only [true_and, and_true, word_one, word_gen]
    exact ⟨l6, l9, l11, l14, hK, hnext⟩
  · exact absurd hok (by simp)

/-- **An index loop** runs its `m` iterations from their honest words. -/
theorem idx_complete {self : String} (hok : idxOk self = true) {N ch z fac : E} {m : ℕ}
    (hm0 : 0 < m) (hN : N = gen ^ m) (hB : ∀ j < m, IdxBody rd ch z fac (gen ^ j)) :
    coreProgram.Rel rd self [1, N, ch, z, fac] [] :=
  Main.loop_complete hm0 hN hB fun d j hj hK hnext => idx_back hok d j hK hj hnext

/-- `__loop80`'s iteration at `x`. -/
def PeqBody (rd : Reader) (peq zeta chi x : E) : Prop :=
  ∃ p z c, LoadHolds rd (peq * x) 0 p ∧ LoadHolds rd (zeta * x) 0 z ∧
    LoadHolds rd (chi * x) 0 c ∧ LoadHolds rd (peq * x) 1 (p * (1 + z + c))

theorem loop80_back {N peq zeta chi : E} (d j : ℕ) (hK : IsInK (gen ^ j * gen + N))
    (hB : PeqBody rd peq zeta chi (gen ^ j))
    (hnext : gen ^ j * gen + N ≠ 0 → coreProgram.relN rd d "__loop80" [gen ^ j * gen, N, peq, zeta, chi] []) :
    coreProgram.relN rd (d + 1) "__loop80" [gen ^ j, N, peq, zeta, chi] [] := by
  obtain ⟨p, z, c, l6, l9, l12, l14⟩ := hB
  set x := gen ^ j
  rw [relN_succ_iff find_loop80]
  refine ⟨setl (Val.ofArgs [x, N, peq, zeta, chi]) 5 [peq * x, p, word 1 0 0, zeta * x, z,
    word 1 0 0 + z, chi * x, c, word 1 0 0 + z + c, p * (word 1 0 0 + z + c), peq * x, word 2 0 0,
    x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by
      simp only [show Fn.params Data.core139 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
        List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core139 = Data.core139.body from rfl, Data.core139.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  b1_look
  simp only [true_and, and_true, word_one, word_gen]
  exact ⟨l6, l9, l12, l14, hK, hnext⟩

/-- **`__loop80`** runs its `m` iterations from their honest words. -/
theorem loop80_complete {peq zeta chi : E} {m : ℕ} (hm0 : 0 < m)
    (hB : ∀ j < m, PeqBody rd peq zeta chi (gen ^ j)) :
    coreProgram.Rel rd "__loop80" [1, gen ^ m, peq, zeta, chi] [] :=
  Main.loop_complete hm0 rfl hB fun d j hj hK hnext => loop80_back d j hK hj hnext

theorem loop79_back {N rounds chi gn cprod : E} (d j : ℕ) {cv cv' : Digest}
    {cur claim claim' rk q c : E}
    (h0 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 0 (digestScalars cv).1)
    (h1 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 1 (digestScalars cv).2)
    (h2 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 2 cur)
    (h3 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 3 claim)
    (hq : gn * wInvG = q * gen ^ j) (hrk : LoadHolds rd (chi * q) 0 rk)
    (h4 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 4 (digestScalars cv').1)
    (h5 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 5 (digestScalars cv').2)
    (h6 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 6 (cur * gen ^ 3))
    (h7 : LoadHolds rd (rounds * (gen ^ j) ^ 4) 7 claim')
    (hc0 : LoadHolds rd (cprod * gen ^ j) 0 c) (hc1 : LoadHolds rd (cprod * gen ^ j) 1 (c * rk))
    (hsc : coreProgram.relN rd d "sumcheck_round4" [(digestScalars cv).1, (digestScalars cv).2, cur, claim]
      [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 3, claim', rk])
    (hK : IsInK (gen ^ j * gen + N))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.relN rd d "__loop79" [gen ^ j * gen, N, rounds, chi, gn, cprod] []) :
    coreProgram.relN rd (d + 1) "__loop79" [gen ^ j, N, rounds, chi, gn, cprod] [] := by
  set x := gen ^ j
  have e8 : rounds * (x * x * (x * x)) = rounds * x ^ 4 := by ring
  rw [relN_succ_iff find_loop79]
  refine ⟨setl (Val.ofArgs [x, N, rounds, chi, gn, cprod]) 6 [x * x, x * x * (x * x),
    rounds * (x * x * (x * x)), (digestScalars cv).1, (digestScalars cv).2, cur, claim,
    (digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 3, claim', rk, wInvG, gn * wInvG, q,
    chi * q, cprod * x, c, c * rk, cprod * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N,
    word 2 0 0, x * word 2 0 0], by
      simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
        List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core138 = Data.core138.body from rfl, Data.core138.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true, e8]
  exact ⟨h0, h1, h2, h3, hsc, hq, hrk, h4, h5, h6, h7, hc0, hc1, hK, hnext⟩

/-- **`__loop79`**, the table sumcheck's rounds, from the honest round states. -/
theorem loop79_complete {rounds chi gn cprod : E} {m : ℕ} (hm0 : 0 < m)
    (hB : ∀ j < m, ZcRound rd rounds chi gn cprod (gen ^ j)) :
    coreProgram.Rel rd "__loop79" [1, gen ^ m, rounds, chi, gn, cprod] [] := by
  choose cv cur claim c0 c2 c3 claim' rk cv' q c h0 h1 h2 h3 hrd hrun hq hrk h4 h5 h6 h7 hc0 hc1 using
    fun j (hj : j < m) => hB j hj
  have hsc : ∀ j (hj : j < m), coreProgram.Rel rd "sumcheck_round4"
      [(digestScalars (cv j hj)).1, (digestScalars (cv j hj)).2, cur j hj, claim j hj]
      [(digestScalars (cv' j hj)).1, (digestScalars (cv' j hj)).2, cur j hj * gen ^ 3,
        claim' j hj, rk j hj] := fun j hj => by
    rw [sumcheck_round4_iff]
    exact ⟨cv j hj, c0 j hj, c2 j hj, c3 j hj, claim' j hj, rk j hj, cv' j hj, rfl, hrd j hj,
      hrun j hj, rfl⟩
  classical
  obtain ⟨D, hD⟩ := Main.rel_uniform (rd := rd) (F := fun _ => "sumcheck_round4")
    (A := fun j => if hj : j < m then [(digestScalars (cv j hj)).1, (digestScalars (cv j hj)).2,
      cur j hj, claim j hj] else [])
    (R := fun j => if hj : j < m then [(digestScalars (cv' j hj)).1,
      (digestScalars (cv' j hj)).2, cur j hj * gen ^ 3, claim' j hj, rk j hj] else []) m
    fun j hj => by simp only [hj, ↓reduceDIte]; exact hsc j hj
  refine Main.loop_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj) ?_
  intro d j hd hj hK hnext
  have := relN_mono coreProgram hd _ _ _ (hD j hj)
  simp only [hj, ↓reduceDIte] at this
  exact loop79_back d j (h0 j hj) (h1 j hj) (h2 j hj) (h3 j hj) (hq j hj) (hrk j hj) (h4 j hj)
    (h5 j hj) (h6 j hj) (h7 j hj) (hc0 j hj) (hc1 j hj) this hK hnext

end
end LeanVM.Guest.B1.VerifySub
