/-
  Rv64mc.Proof.Layout.AddScaledSearchT

  `Form::add_scaled`'s search for where a monomial of `other` goes in `self`'s sorted terms (`partition_point`,
  instructions 25 to 54 and 129 to 161) is total: it loads `self`'s length, compares the monomial with `self`'s
  terms' monomials (lexicographically, word by word) by binary search, and reaches instruction 54 with the index in
  `x27` at most the length, the registers the rest of the body reads (`SKeep`) and the memory unchanged. It stores
  nothing and calls nothing, so its parts take the memory as fixed and the monomials' buffers in windows (`BufT`).

  Three loops, each by `Total.loop`: the word comparison after the search (head 41, measure the words left), the one
  inside the search (head 148, the same), and the binary search (head 135, measure the candidates left).

  ## Main definitions

  * `SKeep`, `AInv`, `BInv`, `HInv`

  ## Main results

  * `loopA`, `final`, `loopB`, `bsearch`, `search`
-/

import Rv64mc.Proof.Layout.FormReprT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Form.AddScaled

namespace Rv64mc.Proof.Layout.AddScaledSearchT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Layout.Form.AddScaled (Link tmpl)

/-- The registers the search keeps: the stack pointer `sp`, `self` (`a`), `other`'s current term (`o`) and end
    (`e`), the constant `1`, `self`'s buffer (`P`) and length (`n`). -/
def SKeep (sp a o e P n : Word) (R : Reg → Word) : Prop :=
  R .x2 = sp ∧ R .x18 = a ∧ R .x19 = o ∧ R .x22 = e ∧ R .x23 = 1#64 ∧ R .x24 = P ∧ R .x25 = n

/-- The comparison after the search at its head (41), `c` words left: the candidate `idx` (`x12`), the two
    monomials' lengths (`x13`, `x10`) and cursors (`x15`, `x11`) `j` words in, the counter `c + 1` (`x14`). -/
def AInv (sp a o e P n idx l1 l2 q1 q2 : Word) (M : MachineState) (c : Nat) (R : Reg → Word) (M' : MachineState) :
    Prop :=
  M' = M ∧ SKeep sp a o e P n R ∧ R .x12 = idx ∧ R .x13 = l1 ∧ R .x10 = l2 ∧ R .x14 = BitVec.ofNat 64 (c + 1) ∧
    c + 1 < 2 ^ 64 ∧ ∃ j, j + c = min l1.toNat l2.toNat ∧ (R .x15).toNat = q1.toNat + 8 * j ∧
      (R .x11).toNat = q2.toNat + 8 * j

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- An unsigned comparison is `0` or `1`. -/
theorem ult_le (a b : Word) : (BinOp.ult.eval a b).toNat ≤ 1 := by
  simp only [BinOp.eval]; split <;> simp

/-- A candidate below the length, plus a comparison, is at most the length. -/
theorem add_ult_le {x n : Word} (a b : Word) (h : x.toNat < n.toNat) : (x + BinOp.ult.eval a b).toNat ≤ n.toNat := by
  have := ult_le a b; have := n.isLt; rw [BitVec.toNat_add]; omega

/-- The counter decremented. -/
theorem cnt_dec {c : Nat} (hc : c + 1 < 2 ^ 64) : (BitVec.ofNat 64 (c + 1) + 18446744073709551615#64).toNat = c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- A monomial's word `j` below its length is in a window and aligned. -/
theorem buf_word {M : MachineState} {l q x : Word} {j : Nat} (hb : BufT env M l q 8)
    (hnx : (env.next M).toNat ≤ 0x78000000) (hj : j < l.toNat) (hx : x.toNat = q.toNat + 8 * j) :
    inWindow x 8 = true ∧ x.toNat % 8 = 0 := by
  rcases hb with h | ⟨h1, h2, h3⟩
  · omega
  · unfold Env.Live at h2
    exact ⟨inWindow_iff.2 (.inl ⟨by omega, by omega⟩), by omega⟩

/-- A word of an object in a window is in a window. -/
theorem inWin_word {a : Word} {n k : Nat} (h : InWin env a n) (hk : k + 8 ≤ n)
    (hW1 : env.heapEnd.toNat ≤ 0x78000000) (hna : 0xa0000000 ≤ env.nextAddr.toNat) :
    inWindow (a + BitVec.ofNat 64 k) 8 = true := by
  have := env.layout
  unfold InWin at h
  rw [inWindow_iff, toNat_add_ofNat (by omega)]
  omega

/-- A candidate's offset, `40` times it. -/
theorem sh40 {x : Word} (h : 40 * x.toNat < 2 ^ 64) : x <<< 5 + x <<< 3 = BitVec.ofNat 64 (40 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := h
  omega

/-- `40` times a candidate, as a number. -/
theorem sh40' {x : Word} (h : 40 * x.toNat < 2 ^ 64) : (x <<< 5 + x <<< 3).toNat = 40 * x.toNat := by
  rw [sh40 h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A term below the length: its monomial a vector. -/
theorem termT {M : MachineState} {P n x : Word} (h : TermsT env M P n.toNat) (hx : x.toNat < n.toNat)
    (hn : 40 * n.toNat < 2 ^ 64) : VecT env M (P + (x <<< 5 + x <<< 3)) 8 := by
  rw [sh40 (by omega)]; exact h _ hx

/-- A cursor advanced by a word, below the end of its monomial. -/
theorem buf_next {M : MachineState} {l q x : Word} {j : Nat} (hb : BufT env M l q 8)
    (hnx : (env.next M).toNat ≤ 0x78000000) (hj : j < l.toNat) (hx : x.toNat = q.toNat + 8 * j) :
    (x + 8#64).toNat = q.toNat + 8 * (j + 1) := by
  rcases hb with h | ⟨h1, h2, h3⟩
  · omega
  · unfold Env.Live at h2
    rw [toNat_add_ofNat (by omega)]; omega

set_option rv_sym.heap true in
/-- **The comparison after the search**, from its head (41) to instruction 54, the index `idx` or `idx + 1`. -/
theorem loopA (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {M : MachineState} {sp a o e P n idx l1 l2 q1 q2 : Word} (hnx : (env.next M).toNat ≤ 0x78000000)
    (hb1 : BufT env M l1 q1 8) (hb2 : BufT env M l2 q2 8) (hidx : idx.toNat < n.toNat)
    (h54 : ∀ R', SKeep sp a o e P n R' → (R' .x27).toNat ≤ n.toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R', M⟩) :
    ∀ c R M', AInv sp a o e P n idx l1 l2 q1 q2 M c R M' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R, M'⟩ := by
  refine Total.loop (I := rvIsa) (AInv sp a o e P n idx l1 l2 q1 q2 M) fun c R M' hI ih => ?_
  obtain ⟨rfl, ⟨k2, k18, k19, k22, k23, k24, k25⟩, h12, h13, h10, h14, hc1, j, hj, h15, h11⟩ := hI
  have hR := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k22 (And.intro k23 (And.intro k24 (And.intro k25
    (And.intro h12 (And.intro h13 (And.intro h10 h14)))))))))
  clear k2 k18 k19 k22 k23 k24 k25 h12 h13 h10 h14
  have hlt : c ≠ 0 → j < l1.toNat ∧ j < l2.toNat := fun h => by omega
  have w15 := fun h => buf_word hb1 hnx (hlt h).1 h15
  have w11 := fun h => buf_word hb2 hnx (hlt h).2 h11
  have e14 := cnt_dec hc1
  have hk : ∀ R', R' .x2 = sp → R' .x18 = a → R' .x19 = o → R' .x22 = e → R' .x23 = 1#64 → R' .x24 = P →
      R' .x25 = n → SKeep sp a o e P n R' := fun _ h1 h2 h3 h4 h5 h6 h7 => ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rv_introT hR
  rv_symT hp stop [108]
  · exact h54 _ (hk _ rfl rfl rfl rfl rfl rfl rfl) (add_ult_le _ _ hidx)
  all_goals try (have hc0 : c ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [e14, h]; rfl)))
  all_goals try (have hc0 : c ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq (by rw [e14, h]; rfl)))
  · exact (w15 hc0).1
  · exact (w15 hc0).2
  · exact (w11 hc0).1
  · exact (w11 hc0).2
  · refine ih (c - 1) _ _ (by omega) ⟨rfl, hk _ rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl,
      BitVec.eq_of_toNat_eq ?_, by omega, j + 1, by omega, buf_next hb1 hnx (hlt hc0).1 h15,
      buf_next hb2 hnx (hlt hc0).2 h11⟩
    simp only [Tactic.rf]; rw [e14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · exact h54 _ (hk _ rfl rfl rfl rfl rfl rfl rfl) (add_ult_le _ _ hidx)

set_option rv_sym.heap true in
/-- **The search's last comparison**, from instruction 31 (pc 62), candidate `idx` below the length: `self`'s term
    `idx`'s monomial against `other`'s, to instruction 54. -/
theorem final (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {M : MachineState} {sp a o e P n idx l2 q2 : Word} (hnx : (env.next M).toNat ≤ 0x78000000)
    (hW1 : env.heapEnd.toNat ≤ 0x78000000) (hna : 0xa0000000 ≤ env.nextAddr.toNat)
    (hT : VecT env M (P + (idx <<< 5 + idx <<< 3)) 8) (hb2 : BufT env M l2 q2 8) (hidx : idx.toNat < n.toNat)
    (h54 : ∀ R', SKeep sp a o e P n R' → (R' .x27).toNat ≤ n.toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R', M⟩) :
    ∀ R, SKeep sp a o e P n R → R .x12 = idx → R .x10 = l2 → R .x11 = q2 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 62, ret, top⟩ :: rest, R, M⟩ := by
  intro R ⟨k2, k18, k19, k22, k23, k24, k25⟩ h12 h10 h11
  have hR := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k22 (And.intro k23 (And.intro k24 (And.intro k25
    (And.intro h12 (And.intro h10 h11))))))))
  clear k2 k18 k19 k22 k23 k24 k25 h12 h10 h11
  obtain ⟨hb1, hle, hcap⟩ := vecT_buf hT
  rw [vecLen_eq, vecPtr_eq] at hb1
  rw [vecLen_eq] at hle
  rw [vecCap_eq] at hle hcap
  have w8 : inWindow (P + (idx <<< 5 + idx <<< 3) + 8#64) 8 = true := inWin_word hT.1 (by decide) hW1 hna
  have w16 : inWindow (P + (idx <<< 5 + idx <<< 3) + 16#64) 8 = true := inWin_word hT.1 (by decide) hW1 hna
  have hA := loopA hp (sp := sp) (a := a) (o := o) (e := e) (P := P) hnx hb1 hb2 hidx h54
  rv_introT hR
  rv_symT hp stop [82]
  all_goals
    simp only [BitVec.lt_def, BitVec.le_def] at hc
    refine hA (min (M.getMem (P + (idx <<< 5 + idx <<< 3) + 16#64)).toNat l2.toNat) _ _ ⟨rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, BitVec.eq_of_toNat_eq ?_, by omega, 0, by omega,
      by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; omega⟩
    simp only [Tactic.rf]
    rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- The comparison inside the search at its head (148), `c` words left: the candidate `mid` (`x12`), the search's
    range (`x13`, `x14`) and half (`x15`), `self`'s monomial's length (`x16`), the counter `c + 1` (`x17`), the
    cursors (`x5`, `x6`) `j` words in. -/
def BInv (sp a o e P n l1 l2 q1 q2 Z B mid h : Word) (M : MachineState) (c : Nat) (R : Reg → Word)
    (M' : MachineState) : Prop :=
  M' = M ∧ SKeep sp a o e P n R ∧ R .x10 = l2 ∧ R .x11 = q2 ∧ R .x12 = mid ∧ R .x13 = Z ∧ R .x14 = B ∧ R .x15 = h ∧
    R .x16 = l1 ∧ R .x17 = BitVec.ofNat 64 (c + 1) ∧ c + 1 < 2 ^ 64 ∧
    ∃ j, j + c = min l1.toNat l2.toNat ∧ (R .x5).toNat = q1.toNat + 8 * j ∧ (R .x6).toNat = q2.toNat + 8 * j

set_option rv_sym.heap true in
/-- **The comparison inside the search**, from its head (148, pc 296) to the search's join (132, pc 264), the
    candidate kept (`self`'s monomial below `other`'s) or the range's start. -/
theorem loopB (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {M : MachineState} {sp a o e P n l1 l2 q1 q2 Z B mid h : Word} (hnx : (env.next M).toNat ≤ 0x78000000)
    (hb1 : BufT env M l1 q1 8) (hb2 : BufT env M l2 q2 8)
    (h264 : ∀ R', SKeep sp a o e P n R' → R' .x10 = l2 → R' .x11 = q2 → (R' .x12 = mid ∨ R' .x12 = B) →
      R' .x13 = Z → R' .x14 = B → R' .x15 = h →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 264, ret, top⟩ :: rest, R', M⟩) :
    ∀ c R M', BInv sp a o e P n l1 l2 q1 q2 Z B mid h M c R M' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 296, ret, top⟩ :: rest, R, M'⟩ := by
  refine Total.loop (I := rvIsa) (BInv sp a o e P n l1 l2 q1 q2 Z B mid h M) fun c R M' hI ih => ?_
  obtain ⟨rfl, ⟨k2, k18, k19, k22, k23, k24, k25⟩, h10, h11, h12, h13, h14, h15, h16, h17, hc1, j, hj, h5, h6⟩ := hI
  have hR := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k22 (And.intro k23 (And.intro k24 (And.intro k25
    (And.intro h10 (And.intro h11 (And.intro h12 (And.intro h13 (And.intro h14 (And.intro h15 (And.intro h16
    h17)))))))))))))
  clear k2 k18 k19 k22 k23 k24 k25 h10 h11 h12 h13 h14 h15 h16 h17
  have hlt : c ≠ 0 → j < l1.toNat ∧ j < l2.toNat := fun h => by omega
  have w5 := fun h => buf_word hb1 hnx (hlt h).1 h5
  have w6 := fun h => buf_word hb2 hnx (hlt h).2 h6
  have e17 := cnt_dec hc1
  rv_introT hR
  rv_symT hp stop [264]
  all_goals try (have hc0 : c ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [e17, h]; rfl)))
  all_goals try (have hc0 : c ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq (by rw [e17, h]; rfl)))
  · exact h264 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (.inl rfl) rfl rfl rfl
  · exact h264 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (.inr rfl) rfl rfl rfl
  · exact (w5 hc0).1
  · exact (w5 hc0).2
  · exact (w6 hc0).1
  · exact (w6 hc0).2
  · refine ih (c - 1) _ _ (by omega) ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      BitVec.eq_of_toNat_eq ?_, by omega, j + 1, by omega, buf_next hb1 hnx (hlt hc0).1 h5,
      buf_next hb2 hnx (hlt hc0).2 h6⟩
    simp only [Tactic.rf]; rw [e17, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · exact h264 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (.inl rfl) rfl rfl rfl
  · exact h264 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (.inr rfl) rfl rfl rfl

/-- The binary search at its head (135), `k` candidates left from `B` (`x13`, `x14`): at least two, within the
    length. -/
def HInv (sp a o e P n l2 q2 : Word) (M : MachineState) (k : Nat) (R : Reg → Word) (M' : MachineState) : Prop :=
  M' = M ∧ SKeep sp a o e P n R ∧ R .x10 = l2 ∧ R .x11 = q2 ∧ (R .x13).toNat = k ∧ 2 ≤ k ∧
    (R .x14).toNat + k ≤ n.toNat

set_option rv_sym.heap true in
/-- **The binary search**, from its head (135, pc 270) to instruction 54. -/
theorem bsearch (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {M : MachineState} {sp a o e P n l2 q2 : Word} (hnx : (env.next M).toNat ≤ 0x78000000)
    (hW1 : env.heapEnd.toNat ≤ 0x78000000) (hna : 0xa0000000 ≤ env.nextAddr.toNat)
    (hterms : TermsT env M P n.toNat) (hn40 : 40 * n.toNat < 2 ^ 64) (hb2 : BufT env M l2 q2 8)
    (h54 : ∀ R', SKeep sp a o e P n R' → (R' .x27).toNat ≤ n.toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R', M⟩) :
    ∀ k R M', HInv sp a o e P n l2 q2 M k R M' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 270, ret, top⟩ :: rest, R, M'⟩ := by
  refine Total.loop (I := rvIsa) (HInv sp a o e P n l2 q2 M) fun k R M' hI ih => ?_
  obtain ⟨rfl, ⟨k2, k18, k19, k22, k23, k24, k25⟩, h10, h11, h13, hk2, h14⟩ := hI
  have hR := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k22 (And.intro k23 (And.intro k24 (And.intro k25
    (And.intro h10 h11)))))))
  clear k2 k18 k19 k22 k23 k24 k25 h10 h11
  have ehalf : (R .x13 >>> 1).toNat = k / 2 := by
    rw [BitVec.toNat_ushiftRight, h13, Nat.shiftRight_eq_div_pow]
  have erest : (R .x13 - R .x13 >>> 1).toNat = k - k / 2 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ehalf, h13]; omega), ehalf, h13]
  have hmid : (R .x13 >>> 1 + R .x14).toNat = k / 2 + (R .x14).toNat := by
    rw [BitVec.toNat_add, ehalf]; have := n.isLt; omega
  have h264 : ∀ v : Word, v.toNat + (k - k / 2) ≤ n.toNat → ∀ R', SKeep sp a o e P n R' → R' .x10 = l2 →
      R' .x11 = q2 → R' .x12 = v → R' .x13 = R .x13 → R' .x14 = R .x14 → R' .x15 = R .x13 >>> 1 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 264, ret, top⟩ :: rest, R', M'⟩ := by
    intro v hv R' ⟨k2, k18, k19, k22, k23, k24, k25⟩ h10 h11 h12 h13' h14' h15
    have hR' := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k22 (And.intro k23 (And.intro k24
      (And.intro k25 (And.intro h10 (And.intro h11 (And.intro h12 (And.intro h13' (And.intro h14' h15)))))))))))
    clear k2 k18 k19 k22 k23 k24 k25 h10 h11 h12 h13' h14' h15
    have hvn : v.toNat < n.toNat := by omega
    rv_introT hR'
    rv_symT hp stop [62, 270]
    · exact final hp hnx hW1 hna (termT hterms hvn hn40) hb2 hvn h54 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
    · rw [BitVec.lt_def, erest] at hc
      exact ih (k - k / 2) _ _ (by omega) ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, erest,
        by simp only [BitVec.toNat_ofNat] at hc; omega, by simp only [Tactic.rf]; omega⟩
  have hmn : (R .x13 >>> 1 + R .x14).toNat < n.toNat := by omega
  have hT := termT hterms hmn hn40
  obtain ⟨hb1, hle, hcap⟩ := vecT_buf hT
  rw [vecLen_eq, vecPtr_eq] at hb1
  rw [vecLen_eq] at hle
  rw [vecCap_eq] at hle hcap
  have hal := hT.2.1.2.1
  have w8 : inWindow (P + ((R .x13 >>> 1 + R .x14) <<< 5 + (R .x13 >>> 1 + R .x14) <<< 3) + 8#64) 8 = true :=
    inWin_word hT.1 (by decide) hW1 hna
  have w16 : inWindow (P + ((R .x13 >>> 1 + R .x14) <<< 5 + (R .x13 >>> 1 + R .x14) <<< 3) + 16#64) 8 = true :=
    inWin_word hT.1 (by decide) hW1 hna
  have hlt := vecT_lt hT
  have hB := loopB hp (sp := sp) (a := a) (o := o) (e := e) (P := P) (n := n) (mid := R .x13 >>> 1 + R .x14)
    (B := R .x14) (Z := R .x13) (h := R .x13 >>> 1) hnx hb1 hb2 fun R' hk h10 h11 h12 h13' h14' h15 => by
      rcases h12 with h12 | h12
      · exact h264 _ (by omega) R' hk h10 h11 h12 h13' h14' h15
      · exact h264 _ (by omega) R' hk h10 h11 h12 h13' h14' h15
  rv_introT hR
  rv_symT hp stop [296]
  all_goals
    simp only [BitVec.lt_def, BitVec.le_def] at hc
    refine hB (min (M'.getMem (P + ((R .x13 >>> 1 + R .x14) <<< 5 + (R .x13 >>> 1 + R .x14) <<< 3) +
      16#64)).toNat l2.toNat) _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      BitVec.eq_of_toNat_eq ?_, by omega, 0, by omega, by simp only [Tactic.rf]; omega,
      by simp only [Tactic.rf]; omega⟩
    simp only [Tactic.rf]
    rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

set_option rv_sym.heap true in
/-- **The search**, from the outer loop's head (25, pc 50) to instruction 54: the index where `other`'s term `o`'s
    monomial goes in `self`'s terms (`a`), at most `self`'s length. -/
theorem search (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {M : MachineState} {sp a o e : Word} (hnx : (env.next M).toNat ≤ 0x78000000)
    (hW1 : env.heapEnd.toNat ≤ 0x78000000) (hna : 0xa0000000 ≤ env.nextAddr.toNat)
    (hself : FormT env M a) (ho : VecT env M o 8)
    (h54 : ∀ R', SKeep sp a o e (M.getMem (a + 8#64)) (M.getMem (a + 16#64)) R' →
      (R' .x27).toNat ≤ (M.getMem (a + 16#64)).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R', M⟩) :
    ∀ R, R .x2 = sp → R .x18 = a → R .x19 = o → R .x22 = e → R .x23 = 1#64 → R .x24 = M.getMem (a + 8#64) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩ := by
  intro R k2 k18 k19 k22 k23 k24
  have hR := And.intro k2 (And.intro k18 (And.intro k19 (And.intro k22 (And.intro k23 k24))))
  clear k2 k18 k19 k22 k23 k24
  have hterms := hself.2
  rw [vecPtr_eq, vecLen_eq] at hterms
  have hn40 : 40 * (M.getMem (a + 16#64)).toNat < 2 ^ 64 := by
    have h := vecT_buf hself.1
    rw [vecLen_eq, vecCap_eq] at h
    omega
  have hbo := (vecT_buf ho).1
  rw [vecLen_eq, vecPtr_eq] at hbo
  have wa : inWindow (a + 16#64) 8 = true := inWin_word hself.1.1 (by decide) hW1 hna
  have wo8 : inWindow (o + 8#64) 8 = true := inWin_word ho.1 (by decide) hW1 hna
  have wo16 : inWindow (o + 16#64) 8 = true := inWin_word ho.1 (by decide) hW1 hna
  have hala := hself.1.2.1.2.1
  have halo := ho.2.1.2.1
  have hla := vecT_lt hself.1
  have hlo := vecT_lt ho
  rv_introT hR
  rv_symT hp stop [62, 108, 270]
  · exact h54 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by simp only [Tactic.rf]; simp)
  · have h0 : (M.getMem (a + 16#64)).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq h)
    have h1 : (M.getMem (a + 16#64)).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq h)
    exact bsearch hp hnx hW1 hna hterms hn40 hbo h54 (M.getMem (a + 16#64)).toNat _ _
      ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, by omega, by simp only [Tactic.rf]; simp⟩
  · have h1 : (M.getMem (a + 16#64)).toNat = 1 := by rw [hc]; rfl
    exact final hp hnx hW1 hna (termT hterms (x := 0#64) (by simp; omega) hn40) hbo (by simp; omega) h54 _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

end Rv64mc.Proof.Layout.AddScaledSearchT
