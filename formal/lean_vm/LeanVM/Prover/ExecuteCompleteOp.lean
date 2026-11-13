module

public import LeanVM.Prover.ExecuteCompleteHint
public import LeanVM.Prover.ExecuteKeccak

/-!
# The executor's instructions are complete

`RefRd rd M`: the reference reader reads `M` at every power below `2^62` it reads, those cells
lying below `maxCells`. `OpModed M s op`: the cells instruction `op` reads at state `s` are written
(for a `MUL`, both operands, or the result and one operand, nonzero in `M`), a `DEREF`'s pointer is
a power below `maxCells` and so is a taken `JUMP`'s frame. Then, if the reference executes the
instruction at the state's registers on `M` to registers whose `pc` is in the program, the
executor's instruction succeeds, keeps `Fine`, extends the memory and moves to those registers
(`runOp_complete`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The reference reader `rd` reads `M` on cells below `maxCells`, and nothing above. -/
def RefRd (rd : K → Option E) (M : ℕ → E) : Prop :=
  ∀ c v, c < 2 ^ 62 → rd (g ^ c) = some v → c < maxCells ∧ M c = v

/-- Registers whose `pc` is in the program. -/
def NextOk (C : Ctx) (r : Registers K) : Prop := ∃ k < C.ops.size, r.pc = g ^ k

/-- What an instruction needs from the state it runs at. -/
def OpModed (M : ℕ → E) (s : St) : Op → Prop
  | .xor a b _ => s.mem.written (s.fp + a) = true ∧ s.mem.written (s.fp + b) = true
  | .mul a b c => (s.mem.written (s.fp + a) = true ∧ s.mem.written (s.fp + b) = true) ∨
    (s.mem.written (s.fp + c) = true ∧ s.mem.written (s.fp + a) = true ∧ M (s.fp + a) ≠ 0) ∨
    (s.mem.written (s.fp + c) = true ∧ s.mem.written (s.fp + b) = true ∧ M (s.fp + b) ≠ 0)
  | .set _ _ => True
  | .deref a _ _ _ => s.mem.written (s.fp + a) = true ∧
    ∃ b < maxCells, (M (s.fp + a)).limb 0 = g ^ b
  | .jump c d f => s.mem.written (s.fp + c) = true ∧ s.mem.written (s.fp + d) = true ∧
    s.mem.written (s.fp + f) = true ∧
    (M (s.fp + c) ≠ 0 → ∃ k < maxCells, (M (s.fp + f)).limb 0 = g ^ k)
  | .keccak ins _ _ _ _ => ∀ i ∈ ins.toList, s.mem.written (s.fp + i) = true

/-- What a completed instruction gives. -/
structure OpDone (C : Ctx) (M : ℕ → E) (s s' : St) (r' : Registers K) : Prop where
  fine : Fine M s'
  le : s.mem ≤ s'.mem
  steps : s'.steps = s.steps
  regs : (⟨g ^ s'.pc, g ^ s'.fp⟩ : Registers K) = r'
  pc : s'.pc < C.ops.size

theorem Agree.read {m : Mem} {M : ℕ → E} (h : Agree m M) {c : ℕ} (hw : m.written c = true) :
    m.read c = .ok (M c) := by
  obtain ⟨v, hv⟩ := Mem.get_of_written hw
  unfold Mem.read
  rw [hv, h.get c v hv]
  rfl

theorem Agree.peek {m : Mem} {M : ℕ → E} (h : Agree m M) {c : ℕ} (hw : m.written c = true) :
    m.peek c = M c := by
  obtain ⟨v, hv⟩ := Mem.get_of_written hw
  rw [Mem.peek_of_get hv, h.get c v hv]

theorem RefRd.at {rd : K → Option E} {M : ℕ → E} (h : RefRd rd M) {fp o : ℕ} {v : E}
    (hfp : fp < maxCells) (ho : o < 2 ^ 28) (hr : rd (g ^ fp * g ^ o) = some v) :
    fp + o < maxCells ∧ M (fp + o) = v := by
  rw [← pow_add] at hr
  exact h _ _ (by unfold maxCells at hfp; omega) hr

theorem next_done {C : Ctx} {M : ℕ → E} {s s' : St} {r' : Registers K} (hs' : Fine M s')
    (hle : s.mem ≤ s'.mem) (hst : s'.steps = s.steps) (hpc : s'.pc = s.pc + 1) (hfp : s'.fp = s.fp)
    (hr : r' = (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K).next) (hnext : NextOk C r')
    (hpc0 : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) : OpDone C M s s' r' := by
  have hr' : r' = ⟨g ^ s'.pc, g ^ s'.fp⟩ := by rw [hr, next_gpow, hpc, hfp]
  refine ⟨hs', hle, hst, hr'.symm, ?_⟩
  obtain ⟨k, hk, hk'⟩ := hnext
  rw [hr'] at hk'
  have := gpow_inj (by omega) (by omega) hk'
  omega

theorem xor_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {a b c : ℕ} (hs : Fine M s) (hrd : RefRd rd M) (hsm : a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28)
    (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ (.xor (g ^ a) (g ^ b) (g ^ c)) = some r')
    (hmo : OpModed M s (.xor a b c)) :
    ∃ s', runOp C s (.xor a b c) = .ok s' ∧ OpDone C M s s' r' := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
  obtain ⟨vA, hA, vB, hB, vC, hC, hg⟩ := hex
  simp [guard] at hg
  obtain ⟨rfl, rfl⟩ := hg
  obtain ⟨ha, hb, hc⟩ := hsm
  obtain ⟨hau, hMa⟩ := hrd.at hs.fp ha hA
  obtain ⟨hbu, hMb⟩ := hrd.at hs.fp hb hB
  obtain ⟨hcu, hMc⟩ := hrd.at hs.fp hc hC
  obtain ⟨m1, e1, h1, le1, -⟩ := hs.agree.put (v := vA + vB) (by rw [hMc]) hcu
  have h2 := (h1.ensure hau).ensure hbu
  refine ⟨{ s with mem := (m1.ensure (s.fp + a)).ensure (s.fp + b), pc := s.pc + 1 }, ?_,
    next_done ⟨h2, hs.dl, hs.small, hs.fp⟩
      (Mem.le_trans le1 (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _))) rfl rfl rfl rfl
      hnext hpc hsz⟩
  simp only [runOp]
  rw [cellAt_eq hau, ok_bind, cellAt_eq hbu, ok_bind, cellAt_eq hcu, ok_bind,
    hs.agree.read hmo.1, hMa, ok_bind, hs.agree.read hmo.2, hMb, ok_bind,
    St.withMem_eq (m := (m1.ensure (s.fp + a)).ensure (s.fp + b)) (by rw [e1]; rfl),
    ok_bind]
  rfl

theorem mul_tail {m0 : Mem} {M : ℕ → E} (h : Agree m0 M) {ca cb cc : ℕ} (wa : m0.written ca = true)
    (wb : m0.written cb = true) (hMc : M cc = M ca * M cb) (hau : ca < maxCells)
    (hbu : cb < maxCells) (hcu : cc < maxCells) :
    ∃ X, (do
      let v := (← m0.read ca) * (← m0.read cb)
      return ((← m0.put cc v).ensure ca).ensure cb : Except Fault Mem) = .ok X ∧ Agree X M ∧
      m0 ≤ X := by
  obtain ⟨m1, e1, h1, le1, -⟩ := h.put hMc hcu
  refine ⟨(m1.ensure ca).ensure cb, ?_, (h1.ensure hau).ensure hbu,
    Mem.le_trans le1 (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _))⟩
  rw [h.read wa, ok_bind, h.read wb, ok_bind]
  dsimp only
  rw [e1]
  rfl

theorem mul_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {a b c : ℕ} (hs : Fine M s) (hrd : RefRd rd M) (hsm : a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28)
    (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ (.mulNative (g ^ a) (g ^ b) (g ^ c)) = some r')
    (hmo : OpModed M s (.mul a b c)) :
    ∃ s', runOp C s (.mul a b c) = .ok s' ∧ OpDone C M s s' r' := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
  obtain ⟨vA, hA, vB, hB, vC, hC, hg⟩ := hex
  simp [guard] at hg
  obtain ⟨rfl, hr⟩ := hg
  obtain ⟨ha, hb, hc⟩ := hsm
  obtain ⟨hau, hMa⟩ := hrd.at hs.fp ha hA
  obtain ⟨hbu, hMb⟩ := hrd.at hs.fp hb hB
  obtain ⟨hcu, hMc⟩ := hrd.at hs.fp hc hC
  have hMc' : M (s.fp + c) = M (s.fp + a) * M (s.fp + b) := by rw [hMa, hMb, hMc]
  have fin : ∀ X, s.mem ≤ X → Agree X M →
      runOp C s (.mul a b c) = .ok { s with mem := X, pc := s.pc + 1 } →
      ∃ s', runOp C s (.mul a b c) = .ok s' ∧ OpDone C M s s' r' := fun X le h e ↦
    ⟨_, e, next_done ⟨h, hs.dl, hs.small, hs.fp⟩ le rfl rfl rfl hr.symm hnext hpc hsz⟩
  by_cases wa : s.mem.written (s.fp + a) = true <;> by_cases wb : s.mem.written (s.fp + b) = true
  · obtain ⟨X, eX, hX, leX⟩ := mul_tail hs.agree wa wb hMc' hau hbu hcu
    refine fin X leX hX ?_
    simp only [runOp]
    rw [cellAt_eq hau, ok_bind, cellAt_eq hbu, ok_bind, cellAt_eq hcu, ok_bind,
      St.withMem_eq (m := X) (by simp only [wa, wb, bne_self_eq_false, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, pure_bind']; exact eX), ok_bind]
    rfl
  · obtain ⟨wc, hna⟩ : s.mem.written (s.fp + c) = true ∧ M (s.fp + a) ≠ 0 := by
      rcases hmo with h | h | h
      · exact absurd h.2 wb
      · exact ⟨h.1, h.2.2⟩
      · exact absurd h.2.1 wb
    have hv : s.mem.peek (s.fp + c) * (M (s.fp + a))⁻¹ = M (s.fp + b) := by
      rw [hs.agree.peek wc, hMc', mul_comm (M (s.fp + a)), mul_assoc, mul_inv_cancel₀ hna, mul_one]
    obtain ⟨m0, e0, h0, le0, g0⟩ := hs.agree.put hv.symm hbu
    obtain ⟨X, eX, hX, leX⟩ := mul_tail h0
      (Option.isSome_iff_exists.mpr ⟨_, le0.get _ _ (Mem.get_of_written wa).choose_spec⟩)
      (Option.isSome_iff_exists.mpr ⟨_, g0⟩) hMc' hau hbu hcu
    refine fin X (Mem.le_trans le0 leX) hX ?_
    simp only [runOp]
    rw [cellAt_eq hau, ok_bind, cellAt_eq hbu, ok_bind, cellAt_eq hcu, ok_bind,
      St.withMem_eq (m := X) (by
        simp only [wa, wb, wc, Bool.true_and, bne_iff_ne, ne_eq, Bool.true_eq_false,
          not_false_eq_true, ↓reduceIte, hs.agree.peek wa, hna]
        rw [e0, ok_bind]; exact eX), ok_bind]
    rfl
  · obtain ⟨wc, hnb⟩ : s.mem.written (s.fp + c) = true ∧ M (s.fp + b) ≠ 0 := by
      rcases hmo with h | h | h
      · exact absurd h.1 wa
      · exact absurd h.2.1 wa
      · exact ⟨h.1, h.2.2⟩
    have hv : s.mem.peek (s.fp + c) * (M (s.fp + b))⁻¹ = M (s.fp + a) := by
      rw [hs.agree.peek wc, hMc', mul_assoc, mul_inv_cancel₀ hnb, mul_one]
    obtain ⟨m0, e0, h0, le0, g0⟩ := hs.agree.put hv.symm hau
    obtain ⟨X, eX, hX, leX⟩ := mul_tail h0 (Option.isSome_iff_exists.mpr ⟨_, g0⟩)
      (Option.isSome_iff_exists.mpr ⟨_, le0.get _ _ (Mem.get_of_written wb).choose_spec⟩)
      hMc' hau hbu hcu
    refine fin X (Mem.le_trans le0 leX) hX ?_
    simp only [runOp]
    rw [cellAt_eq hau, ok_bind, cellAt_eq hbu, ok_bind, cellAt_eq hcu, ok_bind,
      St.withMem_eq (m := X) (by
        simp only [wa, wb, wc, Bool.true_and, bne_iff_ne, ne_eq, Bool.false_eq_true,
          not_false_eq_true, ↓reduceIte, hs.agree.peek wb, hnb]
        rw [e0, ok_bind]; exact eX), ok_bind]
    rfl
  · exfalso
    rcases hmo with h | h | h
    · exact wa h.1
    · exact wa h.2.1
    · exact wb h.2.1

theorem set_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {o : ℕ} {k : E} (hs : Fine M s) (hrd : RefRd rd M) (hsm : o < 2 ^ 28)
    (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ (.setConstant (g ^ o) k) = some r') :
    ∃ s', runOp C s (.set o k) = .ok s' ∧ OpDone C M s s' r' := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
  obtain ⟨v, hv, hg⟩ := hex
  simp [guard] at hg
  obtain ⟨rfl, rfl⟩ := hg
  obtain ⟨hou, hMo⟩ := hrd.at hs.fp hsm hv
  obtain ⟨m1, e1, h1, le1, -⟩ := hs.agree.put hMo hou
  refine ⟨{ s with mem := m1, pc := s.pc + 1 }, ?_,
    next_done ⟨h1, hs.dl, hs.small, hs.fp⟩ le1 rfl rfl rfl rfl hnext hpc hsz⟩
  simp only [runOp]
  rw [cellAt_eq hou, ok_bind, St.withMem_eq (m := m1) e1, ok_bind]
  rfl

theorem deref_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {o1 o2 o3 : ℕ} {mode : DerefMode} (hs : Fine M s) (hrd : RefRd rd M)
    (hsm : o1 < 2 ^ 28 ∧ o2 < 2 ^ 28 ∧ o3 < 2 ^ 28)
    (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ (.deref (g ^ o1) (g ^ o2) (g ^ o3) mode) = some r')
    (hmo : OpModed M s (.deref o1 o2 o3 mode)) :
    ∃ s', runOp C s (.deref o1 o2 o3 mode) = .ok s' ∧ OpDone C M s s' r' := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
  obtain ⟨p, hp, u, hu, v3, h3, v2, h2, hg⟩ := hex
  simp [guard] at hu hg
  obtain ⟨hv, hr⟩ := hg
  obtain ⟨ho1, ho2, ho3⟩ := hsm
  obtain ⟨w1, b, hb, hpb⟩ := hmo
  obtain ⟨a1u, hM1⟩ := hrd.at hs.fp ho1 hp
  obtain ⟨a3u, hM3⟩ := hrd.at hs.fp ho3 h3
  rw [hM1] at hpb
  rw [hpb] at h2
  obtain ⟨a2u, hM2⟩ := hrd.at hb ho2 h2
  have hpK : p.limb 1 = 0 := hu
  obtain ⟨D', eD, hD1, hD2⟩ := St.logOr_complete hs.dl hs.small (f := .wildPointer p) hb
    (by unfold maxCells; norm_num)
  have fin : ∀ m0, s.mem ≤ m0 → Agree m0 M →
      runOp C s (.deref o1 o2 o3 mode) = .ok { s with
        mem := ((m0.ensure (s.fp + o1)).ensure (b + o2)).ensure (s.fp + o3), dl := D',
        pc := s.pc + 1 } →
      ∃ s', runOp C s (.deref o1 o2 o3 mode) = .ok s' ∧ OpDone C M s s' r' := fun m0 le h e ↦
    ⟨_, e, next_done ⟨((h.ensure a1u).ensure a2u).ensure a3u, hD1, hD2, hs.fp⟩
      (Mem.le_trans le (Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _))
        (Mem.le_ensure _ _))) rfl rfl rfl hr.symm hnext hpc hsz⟩
  have hpre : ∀ X (F : Mem → Except Fault Mem), F s.mem = .ok X →
      (do
        let s' ← ({ s with dl := D' } : St).withMem F
        pure { s' with pc := s.pc + 1 } : Except Fault St) =
        .ok { s with mem := X, dl := D', pc := s.pc + 1 } := fun X F hF ↦ by
    rw [St.withMem_eq (s := { s with dl := D' }) (m := X) hF, ok_bind]; rfl
  cases mode with
  | cell =>
    have hM23 : M (b + o2) = M (s.fp + o3) := by rw [hM2, hM3]; exact hv
    by_cases w2 : s.mem.written (b + o2) = true
    · obtain ⟨m0, e0, h0, le0, -⟩ := hs.agree.put (v := s.mem.peek (b + o2))
        (by rw [hs.agree.peek w2, hM23]) a3u
      refine fin m0 le0 h0 ?_
      simp only [runOp]
      rw [cellAt_eq a1u, ok_bind, hs.agree.read w1, hM1, ok_bind]
      simp only [ne_eq, hpK, not_true_eq_false, ↓reduceIte, hpb]
      rw [eD, ok_bind]
      dsimp only
      rw [cellAt_eq a2u, ok_bind, cellAt_eq a3u, ok_bind]
      refine hpre _ _ ?_
      simp only [w2, ↓reduceIte]; rw [e0, ok_bind]; rfl
    · by_cases w3 : s.mem.written (s.fp + o3) = true
      · obtain ⟨m0, e0, h0, le0, -⟩ := hs.agree.put (v := s.mem.peek (s.fp + o3))
          (by rw [hs.agree.peek w3, hM23]) a2u
        refine fin m0 le0 h0 ?_
        simp only [runOp]
        rw [cellAt_eq a1u, ok_bind, hs.agree.read w1, hM1, ok_bind]
        simp only [ne_eq, hpK, not_true_eq_false, ↓reduceIte, hpb]
        rw [eD, ok_bind]
        dsimp only
        rw [cellAt_eq a2u, ok_bind, cellAt_eq a3u, ok_bind]
        refine hpre _ _ ?_
        simp only [w2, w3, Bool.false_eq_true, ↓reduceIte]; rw [e0, ok_bind]; rfl
      · have g2 := Mem.get_of_not_written w2
        have g3 := Mem.get_of_not_written w3
        refine fin _ (Mem.link_ok hs.agree.wf g2 g3).1 (hs.agree.link g2 g3 hM23 a2u a3u) ?_
        simp only [runOp]
        rw [cellAt_eq a1u, ok_bind, hs.agree.read w1, hM1, ok_bind]
        simp only [ne_eq, hpK, not_true_eq_false, ↓reduceIte, hpb]
        rw [eD, ok_bind]
        dsimp only
        rw [cellAt_eq a2u, ok_bind, cellAt_eq a3u, ok_bind]
        refine hpre _ _ ?_
        simp only [w2, w3, Bool.false_eq_true, ↓reduceIte]; rfl
  | pc =>
    obtain ⟨m0, e0, h0, le0, -⟩ := hs.agree.put (v := ofK (g ^ (s.pc + 2)))
      (by rw [hM2, hv]; simp only [derefSource, pow_add, mul_comm]) a2u
    refine fin m0 le0 h0 ?_
    simp only [runOp]
    rw [cellAt_eq a1u, ok_bind, hs.agree.read w1, hM1, ok_bind]
    simp only [ne_eq, hpK, not_true_eq_false, ↓reduceIte, hpb]
    rw [eD, ok_bind]
    dsimp only
    rw [cellAt_eq a2u, ok_bind, cellAt_eq a3u, ok_bind]
    refine hpre _ _ ?_
    rw [e0, ok_bind]; rfl
  | fp =>
    obtain ⟨m0, e0, h0, le0, -⟩ := hs.agree.put (v := ofK (g ^ s.fp)) (by rw [hM2, hv]; rfl) a2u
    refine fin m0 le0 h0 ?_
    simp only [runOp]
    rw [cellAt_eq a1u, ok_bind, hs.agree.read w1, hM1, ok_bind]
    simp only [ne_eq, hpK, not_true_eq_false, ↓reduceIte, hpb]
    rw [eD, ok_bind]
    dsimp only
    rw [cellAt_eq a2u, ok_bind, cellAt_eq a3u, ok_bind]
    refine hpre _ _ ?_
    rw [e0, ok_bind]; rfl

theorem inK_of {what : String} {v : E} (h : v.limb 1 = 0) : inK what v = .ok (v.limb 0) := by
  unfold inK; rw [ite_eq_left h]; rfl

theorem jump_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {c d f : ℕ} (hs : Fine M s) (hrd : RefRd rd M) (hsm : c < 2 ^ 28 ∧ d < 2 ^ 28 ∧ f < 2 ^ 28)
    (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ (.jump (g ^ c) (g ^ d) (g ^ f)) = some r')
    (hmo : OpModed M s (.jump c d f)) :
    ∃ s', runOp C s (.jump c d f) = .ok s' ∧ OpDone C M s s' r' := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
  obtain ⟨vc, hc, vd, hd, vf, hf, u, hu, hg⟩ := hex
  simp [guard] at hu hg
  obtain ⟨hcK, hdK, hfK⟩ := hu
  obtain ⟨hoc, hod, hof⟩ := hsm
  obtain ⟨wc, wd, wf, hjf⟩ := hmo
  obtain ⟨cu, hMc⟩ := hrd.at hs.fp hoc hc
  obtain ⟨du, hMd⟩ := hrd.at hs.fp hod hd
  obtain ⟨fu, hMf⟩ := hrd.at hs.fp hof hf
  have hX := ((hs.agree.ensure cu).ensure du).ensure fu
  have hle : s.mem ≤ ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f) :=
    Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  have hpre : runOp C s (.jump c d f) = (if vc.limb 0 = 0 then
      pure { s with
        mem := ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f), pc := s.pc + 1 }
      else do
        let (pc, s1) ← ({ s with
          mem := ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f) } : St).logOr
          (vd.limb 0) C.ops.size (.notAGPower "JUMP target" (vd.limb 0))
        let (fp, s2) ← s1.logOr (vf.limb 0) maxCells (.notAGPower "JUMP fp" (vf.limb 0))
        pure { s2 with pc, fp }) := by
    simp only [runOp]
    rw [cellAt_eq cu, ok_bind, cellAt_eq du, ok_bind, cellAt_eq fu, ok_bind,
      hs.agree.read wc, hMc, ok_bind, inK_of hcK, ok_bind, hs.agree.read wd, hMd, ok_bind,
      inK_of hdK, ok_bind, hs.agree.read wf, hMf, ok_bind, inK_of hfK, ok_bind,
      St.withMem_eq (m := ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f)) rfl,
      ok_bind]
  by_cases h0 : vc = 0
  · rw [ite_eq_left h0] at hg
    refine ⟨{ s with
      mem := ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f), pc := s.pc + 1 },
      by rw [hpre, ite_eq_left (by rw [h0, limb_zero])]; rfl,
      next_done ⟨hX, hs.dl, hs.small, hs.fp⟩ hle rfl rfl rfl hg.symm hnext hpc hsz⟩
  · rw [ite_eq_right h0] at hg
    have h0' : vc.limb 0 ≠ 0 := fun h ↦ h0 (eq_zero_of_limbs h hcK)
    obtain ⟨k, hk, hkpc⟩ := hnext
    rw [← hg] at hkpc
    obtain ⟨k', hk', hkf⟩ := hjf (by rw [hMc]; exact h0)
    rw [hMf] at hkf
    dsimp only at hkpc
    set s1 : St := { s with mem := ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f) }
    have f1 : Fine M s1 := ⟨hX, hs.dl, hs.small, hs.fp⟩
    obtain ⟨D1, e1, d11, d12⟩ := St.logOr_complete (s := s1) f1.dl f1.small
      (f := .notAGPower "JUMP target" (g ^ k)) hk hsz
    obtain ⟨D2, e2, d21, d22⟩ := St.logOr_complete (s := { s1 with dl := D1 }) d11 d12
      (f := .notAGPower "JUMP fp" (g ^ k')) hk' (by unfold maxCells; norm_num)
    refine ⟨{ s1 with dl := D2, pc := k, fp := k' }, ?_, ⟨hX, d21, d22, hk'⟩, hle, rfl, ?_, hk⟩
    · rw [hpre, ite_eq_right h0', hkpc, e1, ok_bind]
      dsimp only
      rw [hkf, e2, ok_bind]
      rfl
    · rw [← hg, ← hkpc, ← hkf]

end

end LeanVM.Prover.Exec
