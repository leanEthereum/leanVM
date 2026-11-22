/-
  LeanVM.Guest.B1.Gkr.GlCRound

  A GKR round (`gkRoundN`) and a run of them (`glRounds`) on their forward-evaluation equations:
  with the round's words at the cursor, its eq factor at `pt[q]` and its challenge at
  `npt[noff + q]`, the round holds and its values are `gkrRun`'s.
-/

module

public import LeanVM.Guest.B1.Gkr.GlT
public import LeanVM.Guest.B1.Gkr.EvalC
public import LeanVM.Guest.B1.Gkr.Round
public import LeanVM.Guest.B1.Sumcheck.Gkr

/-!
# GKR rounds, completely

* `glc_round`: on its equations (`GoodS`), its five reads not stores, its words, its eq factor
  and its challenge's cell in memory, round `q` from value `B` holds, its challenge, capacity
  and claim one round of `gkrRun` from the carried capacity and claim.
* `glc_rounds`: `n` rounds (`glRounds`), likewise `gkrRun` of `n` rounds.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {S : List Atom}
  {w : ℕ → E}

/-- **One round on its equations.** -/
theorem glc_round {B q cur pt npt noff : ℕ} {claimV : V} {cap : List V}
    (hG : ∀ s ∈ gkRoundN B q (.n cur) (.n pt) (.n npt) noff claimV cap, GoodS rd S w σ s)
    (hk0 : some (B, cur, 4 * q) ∉ S.map loadKey)
    (hk1 : some (B + 3, cur, 4 * q + 1) ∉ S.map loadKey)
    (hk2 : some (B + 6, cur, 4 * q + 2) ∉ S.map loadKey)
    (hk3 : some (B + 9, cur, 4 * q + 3) ∉ S.map loadKey)
    (hke : some (B + 25, pt, q) ∉ S.map loadKey)
    {xs : List E} (hxl : xs.length = 4)
    (hw : ∀ i < 4, LoadHolds rd (σ (.n cur)) (4 * q + i) (xs.getD i 0))
    {e : E} (he : LoadHolds rd (σ (.n pt)) q e)
    (hst : LoadHolds rd (σ (.n npt)) (noff + q)
      ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.1) :
    Stmt.HoldsList C rd σ (gkRoundN B q (.n cur) (.n pt) (.n npt) noff claimV cap) True kret ∧
      σ (.n (B + 12)) = ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (B + 20 + k))) =
        ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.2.cap ∧
      σ (.n (B + 38)) = polyEval ((σ claimV + e * sumE xs) :: xs) (σ (.n (B + 12))) := by
  have g : ∀ a, Stmt.atom a ∈ gkRoundN B q (.n cur) (.n pt) (.n npt) noff claimV cap →
      Good rd S w σ a := fun a ha ↦ hG _ ha
  have sub : ∀ (b off : ℕ), fsNextT (.n cur) off b ⊆
      gkRoundN B q (.n cur) (.n pt) (.n npt) noff claimV cap → ∀ s ∈ fsNextT (.n cur) off b,
        GoodS rd S w σ s := fun b off h s hs ↦ hG s (h hs)
  obtain ⟨x0, c0, f0⟩ := fsNextT_good (C := C) (kret := kret)
    (sub B (4 * q) (by intro s hs; simp only [gkRoundN, List.mem_append]; tauto)) hk0 (hw 0 (by omega))
  obtain ⟨x1, c1, f1⟩ := fsNextT_good (C := C) (kret := kret)
    (sub (B + 3) (4 * q + 1) (by intro s hs; simp only [gkRoundN, List.mem_append]; tauto)) hk1
    (hw 1 (by omega))
  obtain ⟨x2, c2, f2⟩ := fsNextT_good (C := C) (kret := kret)
    (sub (B + 6) (4 * q + 2) (by intro s hs; simp only [gkRoundN, List.mem_append]; tauto)) hk2
    (hw 2 (by omega))
  obtain ⟨x3, c3, f3⟩ := fsNextT_good (C := C) (kret := kret)
    (sub (B + 9) (4 * q + 3) (by intro s hs; simp only [gkRoundN, List.mem_append]; tauto)) hk3
    (hw 3 (by omega))
  obtain ⟨e01, e02⟩ := Prod.ext_iff.mp c0
  dsimp only at e01 e02
  obtain ⟨e04, e05⟩ := Prod.ext_iff.mp c1
  obtain ⟨e07, e08⟩ := Prod.ext_iff.mp c2
  obtain ⟨e10, e11⟩ := Prod.ext_iff.mp c3
  simp only [show B + 3 + 1 = B + 4 by omega, show B + 3 + 2 = B + 5 by omega,
    show B + 6 + 1 = B + 7 by omega, show B + 6 + 2 = B + 8 by omega,
    show B + 9 + 1 = B + 10 by omega, show B + 9 + 2 = B + 11 by omega] at e04 e05 e07 e08 e10 e11
  have hxs : xs = [σ (.n B), σ (.n (B + 3)), σ (.n (B + 6)), σ (.n (B + 9))] := by
    rw [list4_eq hxl, x0, x1, x2, x3]
  -- the permutation
  set ins : List V := [V.n (B + 1), V.n (B + 2), V.n (B + 4), V.n (B + 5), V.n (B + 7),
    V.n (B + 8), V.n (B + 10), V.n (B + 11)] ++ cap with hins
  obtain ⟨hk, -⟩ := keccak_good (g (.keccak ins ((List.range 13).map fun k ↦ .n (B + 12 + k))
    false false) (by simp [gkRoundN, keccakA, hins]))
  obtain ⟨hP, -⟩ := ly_keccak (b := B + 12) hk
  have hs := absorbAll_four (cap.map σ) xs hxl
  have hperm : ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).perm = permOf (ins.map σ) := by
    rw [hs, perm_eq_cells _ (by simp [hxl])]
    rw [hxs]
    simp [hins, pendCells, e01, e02, e04, e05, e07, e08, e10, e11, x0, x1, x2, x3]
  set P := ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).perm with hPd
  rw [← hperm] at hP
  have h25 : σ (.n (B + 12)) = challengeOf P :=
    challengeT_value (s0 := .n (B + 12)) (b := B + 12) rfl (hP 0 (by omega))
  -- the arithmetic
  have l26 := good_read (g (.load (.n (B + 25)) (.n pt) q) (by simp [gkRoundN])) hke he
  have a27 : σ (.n (B + 26)) = σ (.n B) + σ (.n (B + 3)) :=
    g (.add (.n (B + 26)) (.n B) (.n (B + 3))) (by simp [gkRoundN])
  have a28 : σ (.n (B + 27)) = σ (.n (B + 26)) + σ (.n (B + 6)) :=
    g (.add (.n (B + 27)) (.n (B + 26)) (.n (B + 6))) (by simp [gkRoundN])
  have a29 : σ (.n (B + 28)) = σ (.n (B + 27)) + σ (.n (B + 9)) :=
    g (.add (.n (B + 28)) (.n (B + 27)) (.n (B + 9))) (by simp [gkRoundN])
  have m30 := good_mul (g (.mul (.n (B + 29)) (.n (B + 25)) (.n (B + 28))) (by simp [gkRoundN]))
    (by omega) (by omega)
  have a31 : σ (.n (B + 30)) = σ claimV + σ (.n (B + 29)) :=
    g (.add (.n (B + 30)) claimV (.n (B + 29))) (by simp [gkRoundN])
  have m32 := good_mul (g (.mul (.n (B + 31)) (.n (B + 12)) (.n (B + 9))) (by simp [gkRoundN]))
    (by omega) (by omega)
  have a33 : σ (.n (B + 32)) = σ (.n (B + 6)) + σ (.n (B + 31)) :=
    g (.add (.n (B + 32)) (.n (B + 6)) (.n (B + 31))) (by simp [gkRoundN])
  have m34 := good_mul (g (.mul (.n (B + 33)) (.n (B + 12)) (.n (B + 32))) (by simp [gkRoundN]))
    (by omega) (by omega)
  have a35 : σ (.n (B + 34)) = σ (.n (B + 3)) + σ (.n (B + 33)) :=
    g (.add (.n (B + 34)) (.n (B + 3)) (.n (B + 33))) (by simp [gkRoundN])
  have m36 := good_mul (g (.mul (.n (B + 35)) (.n (B + 12)) (.n (B + 34))) (by simp [gkRoundN]))
    (by omega) (by omega)
  have a37 : σ (.n (B + 36)) = σ (.n B) + σ (.n (B + 35)) :=
    g (.add (.n (B + 36)) (.n B) (.n (B + 35))) (by simp [gkRoundN])
  have m38 := good_mul (g (.mul (.n (B + 37)) (.n (B + 12)) (.n (B + 36))) (by simp [gkRoundN]))
    (by omega) (by omega)
  have a39 : σ (.n (B + 38)) = σ (.n (B + 30)) + σ (.n (B + 37)) :=
    g (.add (.n (B + 38)) (.n (B + 30)) (.n (B + 37))) (by simp [gkRoundN])
  have h25' : σ (.n (B + 12)) = ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.1 := by
    rw [h25]; rfl
  refine ⟨?_, h25', ?_, ?_⟩
  · unfold gkRoundN
    rw [tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
      tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
      tb_holdsList_append_noRet (by rfl)]
    refine ⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, ⟨hk, trivial⟩⟩, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l26.2, a27, a28, a29, m30, a31, by rw [← h25'] at hst; exact hst, m32, a33, m34, a35,
      m36, a37, m38, a39⟩
  · show _ = capOf P
    simp only [capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append]
    rw [show B + 20 + 0 = B + 12 + 8 by omega, show B + 20 + 1 = B + 12 + 9 by omega,
      show B + 20 + 2 = B + 12 + 10 by omega, show B + 20 + 3 = B + 12 + 11 by omega,
      show B + 20 + 4 = B + 12 + 12 by omega, hP 8 (by omega), hP 9 (by omega),
      hP 10 (by omega), hP 11 (by omega), hP 12 (by omega)]
    rfl
  · rw [a39, m38, a37, m36, a35, m34, a33, m32, a31, m30, a29, a28, a27, l26.1, hxs]
    simp only [polyEval, List.foldr, sumE, List.foldl]
    ring

theorem glcRounds_succ (B n : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) :
    glRounds B (n + 1) cur pt npt noff claim0 cap0 =
      glRounds B n cur pt npt noff claim0 cap0 ++ glRound B cur pt npt noff claim0 cap0 n := by
  simp [glRounds, List.range_succ]

theorem glcRounds_noRet (B n : ℕ) (cur pt npt : V) (noff : ℕ) (claim0 : V) (cap0 : List V) :
    Stmt.noRetList (glRounds B n cur pt npt noff claim0 cap0) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [glcRounds_succ, tb_noRetList_append, ih, glRound, gkRoundN_noRet]; rfl

/-- **`n` rounds on their equations**: round `q` on the words `Cf q` at `cur[4q ..]`, the eq
factor `ef q` at `pt[q]` and its challenge at `npt[noff + q]`; the claim and the capacity after
`q` rounds are `gkSt`'s. -/
theorem glc_rounds {B cur pt npt noff : ℕ} {claimV : V} {cap : List V} (hcl : cap.length = 5)
    {Cf : ℕ → List E} {ef : ℕ → E} (h4 : ∀ q, (Cf q).length = 4) :
    ∀ n, (∀ s ∈ glRounds B n (.n cur) (.n pt) (.n npt) noff claimV cap, GoodS rd S w σ s) →
      (∀ q < n, some (B + 39 * q, cur, 4 * q) ∉ S.map loadKey ∧
        some (B + 39 * q + 3, cur, 4 * q + 1) ∉ S.map loadKey ∧
        some (B + 39 * q + 6, cur, 4 * q + 2) ∉ S.map loadKey ∧
        some (B + 39 * q + 9, cur, 4 * q + 3) ∉ S.map loadKey ∧
        some (B + 39 * q + 25, pt, q) ∉ S.map loadKey) →
      (∀ q < n, ∀ i < 4, LoadHolds rd (σ (.n cur)) (4 * q + i) ((Cf q).getD i 0)) →
      (∀ q < n, LoadHolds rd (σ (.n pt)) q (ef q)) →
      (∀ q < n, LoadHolds rd (σ (.n npt)) (noff + q)
        (challengeOf (gkP Cf ef (σ claimV) ⟨cap.map σ, []⟩ q))) →
      Stmt.HoldsList C rd σ (glRounds B n (.n cur) (.n pt) (.n npt) noff claimV cap) True kret ∧
        ∀ q, 0 < q → q ≤ n → σ (.n (B + 39 * q - 1)) = (gkSt Cf ef (σ claimV) ⟨cap.map σ, []⟩ q).1 ∧
          (glCap (B + 39 * q - 19)).map σ = (gkSt Cf ef (σ claimV) ⟨cap.map σ, []⟩ q).2.cap
  | 0, _, _, _, _, _ => ⟨trivial, fun q h0 h1 ↦ absurd h1 (by omega)⟩
  | n + 1, hG, hk, hw, he, hst => by
    rw [glcRounds_succ] at hG ⊢
    obtain ⟨ih1, ih2⟩ := glc_rounds hcl h4 n (fun s hs ↦ hG s (List.mem_append_left _ hs))
      (fun q hq ↦ hk q (by omega)) (fun q hq ↦ hw q (by omega)) (fun q hq ↦ he q (by omega))
      (fun q hq ↦ hst q (by omega))
    set St := gkSt Cf ef (σ claimV) ⟨cap.map σ, []⟩ with hSt
    -- the round's carried claim and capacity
    have hin : σ (if n = 0 then claimV else .n (B + 39 * n - 1)) = (St n).1 ∧
        (if n = 0 then cap else glCap (B + 39 * n - 19)).map σ = (St n).2.cap := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hSt, gkSt]
      · have := ih2 n h0 le_rfl
        simp only [show n ≠ 0 by omega, ↓reduceIte]
        exact this
    obtain ⟨k0, k1, k2, k3, ke⟩ := hk n (by omega)
    have hgr : ∀ s ∈ gkRoundN (B + 39 * n) n (.n cur) (.n pt) (.n npt) noff
        (if n = 0 then claimV else .n (B + 39 * n - 1))
        (if n = 0 then cap else glCap (B + 39 * n - 19)), GoodS rd S w σ s :=
      fun s hs ↦ hG s (List.mem_append_right _ (by rw [glRound]; exact hs))
    have hSn : (⟨(if n = 0 then cap else glCap (B + 39 * n - 19)).map σ, []⟩ : Fs) = (St n).2 := by
      rw [hin.2, hSt, gkSt_empty]
    have hP : (((⟨(if n = 0 then cap else glCap (B + 39 * n - 19)).map σ, []⟩ : Fs).absorbAll
        (Cf n) dsObserve).squeeze.1) = challengeOf (gkP Cf ef (σ claimV) ⟨cap.map σ, []⟩ n) := by
      rw [hSn]; rfl
    obtain ⟨hR, h25, hcap, h39⟩ := glc_round (C := C) (kret := kret) hgr
      (by simpa using k0) (by simpa [Nat.add_assoc] using k1) (by simpa [Nat.add_assoc] using k2)
      (by simpa [Nat.add_assoc] using k3) (by simpa [Nat.add_assoc] using ke) (h4 n)
      (hw n (by omega)) (he n (by omega)) (by rw [hP]; exact hst n (by omega))
    refine ⟨(tb_holdsList_append_noRet (glcRounds_noRet _ _ _ _ _ _ _ _)).mpr ⟨ih1, by
      rw [glRound]; exact hR⟩, fun q hq0 hqn ↦ ?_⟩
    rcases Nat.lt_or_ge q (n + 1) with hlt | hge
    · exact ih2 q hq0 (by omega)
    · obtain rfl : q = n + 1 := by omega
      have hstep : St (n + 1) = (polyEval (((St n).1 + ef n * sumE (Cf n)) :: Cf n)
          (((St n).2.absorbAll (Cf n) dsObserve).squeeze.1),
          ((St n).2.absorbAll (Cf n) dsObserve).squeeze.2) := rfl
      rw [hstep, ← hSn]
      refine ⟨?_, ?_⟩
      · rw [show B + 39 * (n + 1) - 1 = B + 39 * n + 38 by omega, h39, h25, hin.1]
      · rw [← hcap, show B + 39 * (n + 1) - 19 = B + 39 * n + 20 by omega]
        simp [glCap]

end
end LeanVM.Guest.B1.Tables
