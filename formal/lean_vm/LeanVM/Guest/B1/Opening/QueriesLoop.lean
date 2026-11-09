/-
  LeanVM.Guest.B1.Opening.QueriesLoop

  The loop helper of `opening_queries`: one iteration's queries and chain step.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesSound
public import LeanVM.Guest.B1.Common.Loops

/-!
# One iteration of `opening_queries`' loop (lean_ethereum.py:1406-1414 at 40f877dc)

* `oqQuery_sound_wins`: a query whose window pointer names a run of a position's windows reads
  them all and opens at that position.
* `oqIter1_sound`, `oqIter0_sound`: an iteration at `x = g^i` opens its queries at the window
  pointers `qptrs[2i + odd]`, `qptrs[2i + odd + 1]` (level 0) or `qptrs[i]` (deeper), and steps
  the chain `chain[i + 1] = ((chain[i] + d0)·μ + d1)·μ` (or `(chain[i] + d)·μ`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## One query, its windows read -/

/-- A run of the windows of a position below `2^depth`. -/
def WinRun (rd : Reader) (bp : E) (depth cd : ℕ) : Prop :=
  ∃ q < 2 ^ depth, FrameRun rd bp (qwN depth cd) fun i ↦ gen ^ qwVal depth cd q i

/-- **A query whose window pointer names a position's windows** reads them and opens at it. -/
theorem oqQuery_sound_wins {s : Oq} (hs : s.RowShape) {walk : String} (hW : WalkSound walk s.pd s.cd)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOkC (coreProgram.Rel rd) rd σ (oqQueryT s bp cap flags wp b emit pr walk))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    (hrun : WinRun rd (σ bp) (s.pd + s.cd) s.cd) :
    ∃ q < 2 ^ (s.pd + s.cd),
      (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (σ bp) i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
        (σ (.n (oqDot s b))) := by
  obtain ⟨q, hq, -, hfr⟩ := hrun
  have hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i := fun i v hv hi ↦ hfr i hi v hv.2
  exact ⟨q, hq, oqQuery_sound hs hW hA hpad hz hq hwin⟩

/-! ## The level-0 iteration -/

theorem oqLoop1A_mem_q1 {s : Oq} {odd : ℕ} {walk : String} {a : Stmt}
    (h : a ∈ oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 walk) :
    a ∈ oqLoop1A s odd walk := by
  simp only [oqLoop1A, List.mem_append]; simp_all

theorem oqLoop1A_mem_q2 {s : Oq} {odd : ℕ} {walk : String} {a : Stmt}
    (h : a ∈ oqQueryT s (.n (oqE1 s)) (.n 3) (.n 4) (.n 5) (oqE1 s + 1) false
      (oqK1 11 s.R + s.D) walk) :
    a ∈ oqLoop1A s odd walk := by
  simp only [oqLoop1A, List.mem_append]; simp_all

/-- **A level-0 iteration** at `x = g^i` (G:1256-1260): its two queries open at the positions the
window pointers `qptrs[2i + odd]`, `qptrs[2i + odd + 1]` name, and the chain steps by their
values. -/
theorem oqIter1_sound {s : Oq} (hs : s.RowShape) {walk : String} (hW : WalkSound walk s.pd s.cd)
    {odd i : ℕ} (hA : BlockOkC (coreProgram.Rel rd) rd σ (oqLoop1A s odd walk)) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ k, k = 2 * i + odd ∨ k = 2 * i + odd + 1 → ∀ bp, LoadHolds rd (σ (.n 2)) k bp →
      WinRun rd bp (s.pd + s.cd) s.cd) :
    ∃ (bp1 bp2 : E) (q1 q2 : ℕ) (r1 r2 : List K) (d0 d1 v : E),
      LoadHolds rd (σ (.n 2)) (2 * i + odd) bp1 ∧ q1 < 2 ^ (s.pd + s.cd) ∧
      (∀ l < qwN (s.pd + s.cd) s.cd, LoadHolds rd bp1 l (gen ^ qwVal (s.pd + s.cd) s.cd q1 l)) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) q1 r1 d0 ∧
      LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) bp2 ∧ q2 < 2 ^ (s.pd + s.cd) ∧
      (∀ l < qwN (s.pd + s.cd) s.cd, LoadHolds rd bp2 l (gen ^ qwVal (s.pd + s.cd) s.cd q2 l)) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) q2 r2 d1 ∧
      LoadHolds rd (σ (.n 6)) i v ∧
      LoadHolds rd (σ (.n 6)) (i + 1) (((v + d0) * σ (.n 7) + d1) * σ (.n 7)) := by
  have p8 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 9) (.n 8) (.n 0)) ∈ _)
  have p10 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n 10) (.n 9) odd) ∈ _)
  have pe1 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n (oqE1 s)) (.n 9) (odd + 1)) ∈ _)
  simp only [Atom.Holds] at p8 p9 p10 pe1
  have h9 : σ (.n 9) = σ (.n 2) * gen ^ (2 * i) := by rw [p9, p8, hx, mul_assoc, ← pow_add]; ring_nf
  rw [h9, loadHolds_mul_gen_pow] at p10 pe1
  -- the queries
  have hq1 := hA.mono fun a h => oqLoop1A_mem_q1 (odd := odd) h
  have hq2 := hA.mono fun a h => oqLoop1A_mem_q2 (odd := odd) h
  obtain ⟨-, -, hpd, -, -⟩ := oqQuery_pieces hq1
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  obtain ⟨q1, hq1lt, hb1, ho1⟩ := oqQuery_sound_wins hs hW hq1 e1 z
    (hbool _ (Or.inl rfl) _ p10)
  obtain ⟨q2, hq2lt, hb2, ho2⟩ := oqQuery_sound_wins hs hW hq2 e1 z
    (hbool (2 * i + odd + 1) (Or.inr rfl) _
      (by rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1))
  -- the chain
  set c := oqC1 s with hc
  have c0 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n c) (.n 6) (.n 0)) ∈ _)
  have c1 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA.atom (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 11))) ∈ _)
  have c3 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)) ∈ _)
  have c4 := hA.atom (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (oqE1 s + 1)))) ∈ _)
  have c5 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 7)) ∈ _)
  have c6 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 6) (.n 0)) ∈ _)
  have c7 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.load (.n (c + 5)) (.n (c + 6)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c6, hx, loadHolds_mul_gen_pow, c5, c4, c3, c2] at c7
  exact ⟨_, _, q1, q2, _, _, _, _, _, p10, hq1lt, hb1, ho1,
    by rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1, hq2lt, hb2, ho2, c1, c7⟩

/-! ## The deeper iteration -/

theorem oqLoop0A_mem_q {s : Oq} {walk : String} {a : Stmt}
    (h : a ∈ oqQueryT s (.n 9) (.n 3) (.n 4) (.n 5) 10 true 0 walk) :
    a ∈ oqLoop0A s walk := by
  simp only [oqLoop0A, List.mem_append]; simp_all

/-- **A deeper iteration** at `x = g^i` (G:1261-1263): its query opens at the position the window
pointer `qptrs[i]` names, and the chain steps by its value. -/
theorem oqIter0_sound {s : Oq} (hs : s.RowShape) {walk : String} (hW : WalkSound walk s.pd s.cd)
    {i : ℕ} (hA : BlockOkC (coreProgram.Rel rd) rd σ (oqLoop0A s walk)) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ bp, LoadHolds rd (σ (.n 2)) i bp → WinRun rd bp (s.pd + s.cd) s.cd) :
    ∃ (bp : E) (q : ℕ) (r : List K) (d v : E),
      LoadHolds rd (σ (.n 2)) i bp ∧ q < 2 ^ (s.pd + s.cd) ∧
      (∀ l < qwN (s.pd + s.cd) s.cd, LoadHolds rd bp l (gen ^ qwVal (s.pd + s.cd) s.cd q l)) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) q r d ∧
      LoadHolds rd (σ (.n 6)) i v ∧ LoadHolds rd (σ (.n 6)) (i + 1) ((v + d) * σ (.n 7)) := by
  have p8 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.load (.n 9) (.n 8) 0) ∈ _)
  simp only [Atom.Holds] at p8 p9
  rw [p8, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p9
  have hq := hA.mono fun a h => oqLoop0A_mem_q h
  obtain ⟨-, -, hpd, -, -⟩ := oqQuery_pieces hq
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  obtain ⟨q, hqlt, hb, ho⟩ := oqQuery_sound_wins hs hW hq e1 z (hbool _ p9)
  set c := oqC0 s with hc
  have c0 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n c) (.n 6) (.n 0)) ∈ _)
  have c1 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA.atom (by simp [oqLoop0A, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 10))) ∈ _)
  have c3 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)) ∈ _)
  have c4 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 4)) (.n 6) (.n 0)) ∈ _)
  have c5 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.load (.n (c + 3)) (.n (c + 4)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c4, hx, loadHolds_mul_gen_pow, c3, c2] at c5
  exact ⟨_, q, _, _, _, p9, hqlt, hb, ho, c1, c5⟩

end
end LeanVM.Guest.B1
