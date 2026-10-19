/-
  LeanVM.Guest.B1.Tables.VerifyTablesTail

  `verify_tables`' last steps: the tables' terms summed into `air_acc` and checked against the
  sumcheck's claim, the public input's challenge and claims, and the returns.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesReads
public import LeanVM.Guest.B1.Tables.VerifyTablesZc

/-!
# The last steps (G:1812-1824)

Each table's `constraint_eval` enters `air_acc` weighted by `cprod[n - τ]·peq[τ]` (`vt_air`); the
total must be the sumcheck's final claim. Then `rm` is squeezed, both public-input words are
split into their canonical limbs, the three public claims are pooled (`vt_pi`), and the function
returns the state, the cursor 104 words on, `g^n`, the bytecode share and `rm`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Each table's `g^τ`, by value number. -/
def airTau : List ℕ := [4660, 5148, 5677, 5954, 6477, 6979]

/-- The first value of each table's weighting, and its first statement. -/
def airQ : List ℕ := [5141, 5669, 5946, 6469, 6971, 8132]
def airStmt : List ℕ := [4855, 5383, 5660, 6183, 6685, 7846]

/-- Each table's `constraint_eval` and first statement. -/
def airCe : List ℕ := [5140, 5668, 5945, 6468, 6970, 8131]
def airStart : List ℕ := [4374, 4862, 5391, 5668, 6191, 6693]

/-- Table `t`'s weighting into `air_acc`, from value `q`: `g^n = q·g^τ`, the loads of
`cprod[q]` and `peq[g^τ]`, their product with `constraint_eval`. -/
def airT (q tau ce : ℕ) : List Stmt :=
  [.atom (.mul (.n 4554) (.n q) (.n tau)), .atom (.mul (.n (q + 1)) (.n 4639) (.n q)),
    .atom (.load (.n (q + 2)) (.n (q + 1)) 0), .atom (.mul (.n (q + 3)) (.n 4655) (.n tau)),
    .atom (.load (.n (q + 4)) (.n (q + 3)) 0), .atom (.mul (.n (q + 5)) (.n (q + 2)) (.n (q + 4))),
    .atom (.mul (.n (q + 6)) (.n (q + 5)) (.n ce))]

/-- `air_acc` after table `t`, by value number. -/
def airAcc (t : ℕ) : ℕ := if t = 0 then 5147 else airQ.getD t 0 + 7

theorem air_blocks : ∀ t < 6, stmtsEqb (airT (airQ.getD t 0) (airTau.getD t 0) (airCe.getD t 0))
      ((vtPre.drop (airStmt.getD t 0)).take 7) = true ∧
    (1 ≤ t → stmtsEqb [.atom (.add (.n (airAcc t)) (.n (airAcc (t - 1))) (.n (airQ.getD t 0 + 6)))]
      ((vtPre.drop (airStmt.getD t 0 + 7)).take 1) = true) ∧
    stmtsEqb [.atom (.load (.n (airTau.getD t 0)) (.n 7) (t + 1))]
      ((vtPre.drop (airStart.getD t 0)).take 1) = true := by
  decide +kernel

theorem gen_pow_cancel {q : E} {a b : ℕ} (hab : b ≤ a) (h : gen ^ a = q * gen ^ b) :
    q = gen ^ (a - b) := by
  have hg : gen ^ b ≠ 0 := pow_ne_zero _ vt_gen_ne_zero
  exact mul_right_cancel₀ hg (by rw [← h, ← pow_add, Nat.sub_add_cancel hab])

/-- **`air_acc`** (G:1812): with the table sumcheck's prefix products in `cprod` and `peq`, each
table's `constraint_eval` enters weighted by `cprod[n - τ]·peq[τ]`. -/
theorem vt_air {rd : Reader} {σ : Val} (h : VtHolds rd σ) {n : ℕ} (τ : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t ≤ n) (hgn : σ (.n 4554) = gen ^ n)
    (htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ τ t) {cp pq : ℕ → E}
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 4639)) j (cp j))
    (hpq : ∀ k ≤ n, LoadHolds rd (σ (.n 4655)) k (pq k)) :
    ∀ t < 6, σ (.n (airAcc t)) = ((List.range (t + 1)).map fun s =>
      cp (n - τ s) * pq (τ s) * σ (.n (airCe.getD s 0))).sum := by
  have hterm : ∀ t < 6, σ (.n (airQ.getD t 0 + 6)) =
      cp (n - τ t) * pq (τ t) * σ (.n (airCe.getD t 0)) := by
    intro t ht
    obtain ⟨hb, -, -⟩ := air_blocks t ht
    obtain ⟨k, hb⟩ := h.slice _ _ hb
    simp only [airT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨m0, m1, l2, m3, l4, m5, m6⟩ := hb
    rw [hgn, htau t ht] at m0
    have hq := gen_pow_cancel (hτ t ht) m0
    rw [m1, hq, loadHolds_gen_pow_mul, Nat.add_zero] at l2
    rw [m3, htau t ht, loadHolds_gen_pow_mul, Nat.add_zero] at l4
    rw [m6, m5, loadHolds_unique l2 (hcp _ (by omega)), loadHolds_unique l4 (hpq _ (hτ t ht))]
  intro t ht
  induction t with
  | zero => simpa [airAcc, airQ] using hterm 0 (by omega)
  | succ t ih =>
    obtain ⟨-, hadd, -⟩ := air_blocks (t + 1) ht
    have ha := h.atom _ _ (hadd (by omega))
    simp only [Atom.Holds, Nat.add_sub_cancel] at ha
    rw [ha, ih (by omega), hterm (t + 1) ht, List.range_succ (n := t + 1), List.map_append,
      List.sum_append]
    simp

theorem word_g104 : word 29686813949952 0 0 = gen ^ 104 := by
  rw [word_ofK, show K.ofBits 29686813949952 = gpowK 104 by decide +kernel,
    gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

theorem vt_pi_blocks :
    stmtsEqb (canonicalLimbsT (.n 3) 8154) ((vtPre.drop 7869).take 5) = true ∧
    stmtsEqb (canonicalLimbsT (.n 4) 8159) ((vtPre.drop 7875).take 5) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The public input's claims and the returns** (G:1814-1824): the accumulated terms are the
sumcheck's claim; from the state of `cvR` at `(7569, 7570)`, `rm` is squeezed; both public
words are canonical and their limbs' lines at `rm` are pooled at `109 .. 111`; the function
returns the new state, the cursor 104 words on, `g^n`, the bytecode share and `rm`. -/
theorem vt_pi {rd : Reader} {σ : Val} (h : VtHolds rd σ) {cvR : Digest}
    (hcv : (σ (.n 7569), σ (.n 7570)) = digestScalars cvR) :
    σ (.n 8139) = σ (.n 4652) ∧ (σ (.n 8145), σ (.n 8146)) = digestScalars (sqCv cvR) ∧
      σ (.n 8153) = challengeOf (sqCv cvR) ∧ IsCanonical128 (σ (.n 3)) ∧
      IsCanonical128 (σ (.n 4)) ∧
      LoadHolds rd (σ (.n 13)) 109 (ofK ((σ (.n 3)).limb 0) +
        σ (.n 8153) * (ofK ((σ (.n 3)).limb 0) + ofK ((σ (.n 4)).limb 0))) ∧
      LoadHolds rd (σ (.n 13)) 110 (ofK ((σ (.n 3)).limb 1) +
        σ (.n 8153) * (ofK ((σ (.n 3)).limb 1) + ofK ((σ (.n 4)).limb 1))) ∧
      LoadHolds rd (σ (.n 13)) 111 0 ∧
      σ (.n 8171) = σ (.n 8145) ∧ σ (.n 8172) = σ (.n 8146) ∧
      σ (.n 8175) = σ (.n 4651) * gen ^ 104 ∧ σ (.n 8176) = σ (.n 4554) ∧
      σ (.n 8177) = σ (.n 1732) ∧ σ (.n 8178) = σ (.n 8153) := by
  have ae := h.atom 7854 (.assertEq (.n 8139) (.n 4652)) (by decide +kernel)
  obtain ⟨cv, hc, hs, hr⟩ := h.squeeze 7855 (.n 7569) (.n 7570) 8140 (by decide +kernel)
  rw [hcv] at hc
  obtain rfl := digestScalars_injective hc
  obtain ⟨k0, b0⟩ := h.slice _ _ vt_pi_blocks.1
  obtain ⟨k1, b1⟩ := h.slice _ _ vt_pi_blocks.2
  rw [holds_canonicalLimbsT] at b0 b1
  obtain ⟨⟨hc0, e8154, -, -, e8157⟩, -⟩ := b0
  obtain ⟨⟨hc1, e8159, -, -, e8162⟩, -⟩ := b1
  have c58 := h.atom 7874 (.copy (.n 8158) (.n 8154)) (by decide +kernel)
  have c63 := h.atom 7880 (.copy (.n 8163) (.n 8159)) (by decide +kernel)
  have a64 := h.atom 7881 (.add (.n 8164) (.n 8158) (.n 8163)) (by decide +kernel)
  have m65 := h.atom 7882 (.mul (.n 8165) (.n 8153) (.n 8164)) (by decide +kernel)
  have a66 := h.atom 7883 (.add (.n 8166) (.n 8158) (.n 8165)) (by decide +kernel)
  have l66 := h.atom 7884 (.load (.n 8166) (.n 13) 109) (by decide +kernel)
  have a67 := h.atom 7885 (.add (.n 8167) (.n 8157) (.n 8162)) (by decide +kernel)
  have m68 := h.atom 7886 (.mul (.n 8168) (.n 8153) (.n 8167)) (by decide +kernel)
  have a69 := h.atom 7887 (.add (.n 8169) (.n 8157) (.n 8168)) (by decide +kernel)
  have l69 := h.atom 7888 (.load (.n 8169) (.n 13) 110) (by decide +kernel)
  have c70 := h.atom 7889 (.const (.n 8170) (word 0 0 0)) (by decide +kernel)
  have l70 := h.atom 7890 (.load (.n 8170) (.n 13) 111) (by decide +kernel)
  have r71 := h.atom 7891 (.copy (.n 8171) (.n 8145)) (by decide +kernel)
  have r72 := h.atom 7892 (.copy (.n 8172) (.n 8146)) (by decide +kernel)
  have c73 := h.atom 7893 (.const (.n 8173) (word 29686813949952 0 0)) (by decide +kernel)
  have m74 := h.atom 7894 (.mul (.n 8174) (.n 4651) (.n 8173)) (by decide +kernel)
  have r75 := h.atom 7895 (.copy (.n 8175) (.n 8174)) (by decide +kernel)
  have r76 := h.atom 7896 (.copy (.n 8176) (.n 4554)) (by decide +kernel)
  have r77 := h.atom 7897 (.copy (.n 8177) (.n 1732)) (by decide +kernel)
  have r78 := h.atom 7898 (.copy (.n 8178) (.n 8153)) (by decide +kernel)
  simp only [Atom.Holds, word_zero] at *
  refine ⟨e_add_eq_zero_iff.mp ae, hs, hr, hc0, hc1, ?_, ?_, by rw [← c70]; exact l70, r71, r72,
    by rw [r75, m74, c73, word_g104], r76, r77, r78⟩
  · rw [a66, m65, a64, c58, c63, e8154, e8159] at l66; exact l66
  · rw [a69, m68, a67, e8157, e8162] at l69; exact l69

end
end LeanVM.Guest.B1.VerifySub
