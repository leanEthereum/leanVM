/-
  LeanVM.Guest.B1.Opening.QueriesPlaced6

  `opening_queries`' loop, placed: its iterations one frame after another.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced5

/-!
# The loop, placed

`oqLoop1_relAtIn`, `oqLoop0_relAtIn`: the loop helper called at `g^j` with the bound `g^N`, placed
at `fp + j·fs loop`, its iteration `j'` at `fp + j'·fs loop` (a loop helper's tail call comes
first, right after its frame), is `RelAtIn` the caller's region `R`, of `(N - j + 1)·fs loop`
words and its walks' frames, when every iteration's data holds (`OqIt1Ok`, `OqIt0Ok`: its queries'
`QD.Ok` with their windows, their points and window pointers, the chain, its region).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **What a level-0 iteration at `g^j` needs**: its two queries honest with their windows, their
points and window pointers, the chain's step (non-final levels), and where it reads the caller's
words. -/
structure OqIt1Ok (rd : Reader) (R : ℕ → Prop) (s : Oq) (odd j : ℕ)
    (positions qptrs cap flags coefs hsp ch mu : E) (rounds : List FoldRound) (hsv : List E)
    (w1 w2 : QW) (bp1 bp2 v : E) : Prop where
  ok1 : (oqQD s 16 true 0 cap flags rounds hsv w1).Ok rd coefs hsp bp1
  ok2 : (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).Ok rd coefs hsp bp2
  x1 : LoadHolds rd positions (2 * j + odd) (eOfNat w1.1)
  x2 : LoadHolds rd positions (2 * j + odd + 1) (eOfNat w2.1)
  b1 : LoadHolds rd qptrs (2 * j + odd) bp1
  b2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2
  chv : s.final ≠ 1 → LoadHolds rd ch j v ∧
    LoadHolds rd ch (j + 1) (((v + oqResV s rounds w1) * mu + oqResV s rounds w2) * mu)
  rp : ∀ e < 2, OqIn R ((positions * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex (odd + e))
  rq : ∀ e < 2, OqIn R ((qptrs * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex (odd + e))
  reg1 : OqQReg R s cap flags coefs hsp bp1 w1.1
  reg2 : OqQReg R s cap flags coefs hsp bp2 w2.1
  rc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)

/-- **What a deeper iteration at `g^j` needs.** -/
structure OqIt0Ok (rd : Reader) (R : ℕ → Prop) (s : Oq) (j : ℕ)
    (positions qptrs cap flags coefs hsp ch mu : E) (rounds : List FoldRound) (hsv : List E)
    (w : QW) (bp v : E) : Prop where
  ok : (oqQD s 14 true 0 cap flags rounds hsv w).Ok rd coefs hsp bp
  x : LoadHolds rd positions j (eOfNat w.1)
  b : LoadHolds rd qptrs j bp
  chv : s.final ≠ 1 → LoadHolds rd ch j v ∧ LoadHolds rd ch (j + 1) ((v + oqResV s rounds w) * mu)
  rp : OqIn R ((positions * gen ^ j).limb 0 * Parameters.addressOfIndex 0)
  rq : OqIn R ((qptrs * gen ^ j).limb 0 * Parameters.addressOfIndex 0)
  reg : OqQReg R s cap flags coefs hsp bp w.1
  rc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)

theorem gen_pow_guard {j N : ℕ} (hN : N < ordG) (hj : j + 1 ≤ N) :
    IsInK (gen ^ j * gen + gen ^ N) ∧ (gen ^ j * gen + gen ^ N ≠ 0 ↔ j + 1 < N) := by
  rw [← pow_succ]
  refine ⟨isInK_add (by rw [gen_pow_eq_ofK]; exact ofK_isInK _)
    (by rw [gen_pow_eq_ofK]; exact ofK_isInK _), ⟨fun h ↦ ?_, fun h he ↦ ?_⟩⟩
  · rcases Nat.lt_or_ge (j + 1) N with h' | h'
    · exact h'
    · exact absurd (by rw [show j + 1 = N by omega]; exact e_add_self _) h
  · have := gen_pow_inj (lt_of_lt_of_le (by omega) (le_of_lt hN)) hN (e_add_eq_zero_iff.mp he)
    omega

/-- **The level-0 loop, placed.** -/
theorem oqLoop1_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    {wlk loop : String}
    (hW : WalkFn wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N < ordG)
    {positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w1 w2 : ℕ → QW} {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd R s odd j positions qptrs cap flags coefs hsp ch mu rounds hsv
      (w1 j) (w2 j) (bp1 j) (bp2 j) (v j)) :
    ∀ j < N, RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + j * fs loop)
      ((N - j + 1) * fs loop + (N - j) * (2 * fs wlk)) loop [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] := by
  suffices h : ∀ n j, j + n + 1 = N → RelAtIn coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) ((N - j + 1) * fs loop + (N - j) * (2 * fs wlk)) loop
      [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      [] from fun j hj ↦ h (N - j - 1) j (by omega)
  intro n
  induction n with
  | zero =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have := oqIter1_relAtIn (fp := fp + j * fs loop) (m := fs loop) hP fs cert hs hfin hpd1 hcd hW hfl hpl hbl hlp
      H.ok1 H.ok2 H.x1 H.x2 H.b1 H.b2 H.chv hK
      (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · rfl) H.rp H.rq H.reg1 H.reg2 H.rc
    rw [show (N - j + 1) * fs loop + (N - j) * (2 * fs wlk) = fs loop + fs loop + 2 * fs wlk by
      rw [show N - j = 1 by omega]; ring]
    exact this
  | succ n ih =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring, pow_succ] at ht
    have := oqIter1_relAtIn (fp := fp + j * fs loop)
      (m := (N - (j + 1) + 1) * fs loop + (N - (j + 1)) * (2 * fs wlk)) hP fs cert hs hfin hpd1 hcd hW hfl
      hpl hbl hlp H.ok1 H.ok2 H.x1 H.x2 H.b1 H.b2 H.chv hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h) H.rp H.rq H.reg1 H.reg2 H.rc
    rw [show (N - j + 1) * fs loop + (N - j) * (2 * fs wlk) = fs loop +
        ((N - (j + 1) + 1) * fs loop + (N - (j + 1)) * (2 * fs wlk)) + 2 * fs wlk by
      rw [show N - j = N - (j + 1) + 1 by omega]; ring]
    exact this

/-- **The deeper loop, placed.** -/
theorem oqLoop0_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    {wlk loop : String}
    (hW : WalkFn wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N < ordG)
    {positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w : ℕ → QW} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd R s j positions qptrs cap flags coefs hsp ch mu rounds hsv
      (w j) (bp j) (v j)) :
    ∀ j < N, RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + j * fs loop)
      ((N - j + 1) * fs loop + (N - j) * fs wlk) loop [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] := by
  suffices h : ∀ n j, j + n + 1 = N → RelAtIn coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) ((N - j + 1) * fs loop + (N - j) * fs wlk) loop
      [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      [] from fun j hj ↦ h (N - j - 1) j (by omega)
  intro n
  induction n with
  | zero =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have := oqIter0_relAtIn (fp := fp + j * fs loop) (m := fs loop) hP fs cert hs hfin hpd1 hcd hW hfl hpl hbl hlp
      H.ok H.x H.b H.chv hK (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · rfl) H.rp H.rq H.reg H.rc
    rw [show (N - j + 1) * fs loop + (N - j) * fs wlk = fs loop + fs loop + fs wlk by
      rw [show N - j = 1 by omega]; ring]
    exact this
  | succ n ih =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring, pow_succ] at ht
    have := oqIter0_relAtIn (fp := fp + j * fs loop)
      (m := (N - (j + 1) + 1) * fs loop + (N - (j + 1)) * fs wlk) hP fs cert hs hfin hpd1 hcd hW hfl
      hpl hbl hlp H.ok H.x H.b H.chv hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h) H.rp H.rq H.reg H.rc
    rw [show (N - j + 1) * fs loop + (N - j) * fs wlk = fs loop +
        ((N - (j + 1) + 1) * fs loop + (N - (j + 1)) * fs wlk) + fs wlk by
      rw [show N - j = N - (j + 1) + 1 by omega]; ring]
    exact this

end
end LeanVM.Guest.B1
