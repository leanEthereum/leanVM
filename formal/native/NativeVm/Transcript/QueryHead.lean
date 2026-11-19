module

public import NativeVm.Transcript.QueryPre

/-!
# `query`'s prelude, run

`queryHead_spec`: from a state that simulates `st`, `query`'s instructions before the openings'
loop (`queryHead`, `query_eq`) take root `i` into the context's `qRootW` words and the next phase,
checked against the positions' count and the root's shape; they fail exactly when one of these
checks does, and then `queryStep` is `none`.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

variable {env : Env} {st : VerifierProgramState} {s : QState} {P E : QState → Prop}

/-- `query`'s instructions before the openings' loop. -/
def queryHead : List Stmt := [
  I (.load .r8 (cw ctxWork)),
  I (.load .rax (at_ .r8 (wdisp workRootCount))),
  failIf (.cmp .geu .r9 (.reg .rax)),
  I (.shli .r9 6),
  blk ((List.range 6).flatMap rootP),
  I (.load .rax (at_ .r8 (wdisp workPhase))), I (.load .rcx (at_ .r8 (wdisp workPhaseCount))),
  failIf (.cmp .geu .rax (.reg .rcx)),
  I (.addi .rax 1), I (.store (at_ .r8 (wdisp workPhase)) .rax),
  I (.load .r13 (at_ .r8 (wdisp workPhasePtr))),
  I (.lea .rax (at_ .r13 (wdisp phaseWords))), I (.store (at_ .r8 (wdisp workPhasePtr)) .rax),
  I (.load .rax (at_ .r13 0)), failIf (.cmp .ne .rax (.reg .r11)),
  .ite (.cmp .eq .r11 (.imm 0)) .skip (blk [
    I (.load .rax (at_ .r13 8)), I (.load .rcx (cw (qRootW + 4))),
    failIf (.cmp .ne .rax (.reg .rcx)),
    I (.load .rax (at_ .r13 16)), I (.load .rcx (cw (qRootW + 5))),
    failIf (.cmp .ne .rax (.reg .rcx))]),
  I (.addi .r13 24)]

theorem query_eq : query = blk (queryHead ++ [.loop (.cmp .ne .r11 (.imm 0)) openOne]) := (rfl)

/-- The rest of a block, its state named. -/
theorem wp_gen {xs : List Stmt} (h : ∀ s', s' = s → WP (blk xs) s' P E) : WP (blk xs) s P E :=
  h s rfl

/-- `queryStep` once the root and the phase are found. -/
theorem queryStep_of {i : Nat} {ps : List Nat} {root : Digest} {height width : Nat}
    {phase : List Opening} {rest : List (List Opening)}
    (hr : st.roots[i]? = some (root, height, width)) (ho : st.openings = phase :: rest) :
    queryStep i ps st = (Id.run (openPhase (m := Id) keccakF1600 root height width ps phase)).map
      fun rows ↦ (rows, { st with openings := rest }) := by
  unfold queryStep
  rw [hr, ho]
  simp only
  generalize Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) = o
  cases o <;> rfl

theorem toUInt64_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    (a.toUInt64 != b.toUInt64) = true :=
  bne_iff_ne.mpr fun e ↦ h ((toUInt64_inj ha hb).mp e)

theorem add16_wd (b : UInt64) (k : Nat) : wd b k + 16 = wd b (k + 2) := by rw [← wd_add]; rfl

theorem add24_wd (b : UInt64) (k : Nat) : wd b k + 24 = wd b (k + 3) := by rw [← wd_add]; rfl

/-- The relation depends on `rdi` and the memory only. -/
theorem SimState.of_mem {s' : QState} (h : SimState env st s) (hm : s'.mem = s.mem)
    (hrdi : s'.reg .rdi = s.reg .rdi) : SimState env st s' := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  rw [← hm] at b c d e f g j k
  exact ⟨hrdi.trans a, b, c, d, e, f, g, i, j, k⟩

theorem phaseBase_succ (L p : Nat) : phaseBase L (p + 1) = phaseBase L p + phaseWords := by
  unfold phaseBase
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **`query`'s prelude.** -/
theorem queryHead_spec {i : Nat} {ps : List Nat} (h : SimState env st s) (hi : i < 2 ^ 64)
    (hn : ps.length < 2 ^ 64) (hr9 : s.reg .r9 = i.toUInt64) (hr11 : s.reg .r11 = ps.length.toUInt64) :
    WP (blk queryHead) s (fun s' ↦ ∃ root height width p, ∃ hp : p < env.proof.openings.length,
        st.roots[i]? = some (root, height, width) ∧ st.openings = env.proof.openings.drop p ∧
        env.proof.openings[p].length = ps.length ∧
        (ps.length ≠ 0 → ∀ o ∈ env.proof.openings[p], o.leaf.length = width ∧ o.path.length = height) ∧
        SimState env { st with openings := env.proof.openings.drop (p + 1) } s' ∧
        (∀ k < 4, s'.mem (wd env.ctx (qRootW + k)) = some (root.toList.getD k 0)) ∧
        s'.mem (wd env.ctx (qRootW + 4)) = some height.toUInt64 ∧
        s'.mem (wd env.ctx (qRootW + 5)) = some width.toUInt64 ∧
        s'.reg .r13 = wd env.dec (phaseBase env.L p + 3) ∧
        (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
        Keep (Foot env) s.mem s'.mem ∧ RegsFrame [.rax, .rcx, .r8, .r9, .r13] s s')
      (fun s' ↦ queryStep i ps st = none ∧ s'.reg .rdi = s.reg .rdi ∧ Keep (Foot env) s.mem s'.mem) := by
  have hL := h.layout
  obtain ⟨p, hp, hpw, hpp, hop⟩ := h.phase
  have hrl := h.rootsLen
  simp only [maxRoots_val] at hrl
  unfold queryHead
  refine wp_load (eval_cw h.rdi _) hL.workPtr ?_
  refine wp_load (work_reg (env := env) (by reg_simp) _) h.rootCount ?_
  by_cases hil : st.roots.length ≤ i
  · refine wp_failIf_fail ?_ ⟨?_, by reg_simp, Keep.refl _ _⟩
    · rw [cond_geu, rhs_reg]
      reg_simp
      rw [hr9]
      exact decide_eq_true ((toUInt64_le (by omega) hi).mpr hil)
    · unfold queryStep
      rw [List.getElem?_eq_none hil]
  have hil' : i < st.roots.length := by omega
  refine wp_failIf (by
    rw [cond_geu, rhs_reg]
    reg_simp
    rw [hr9]
    exact decide_eq_false fun e ↦ hil ((toUInt64_le (by omega) hi).mp e)) ?_
  refine wp_reg rfl ?_
  obtain ⟨⟨root, height, width⟩, hget⟩ : ∃ r, st.roots[i] = r := ⟨_, rfl⟩
  have hR := h.roots i hil'
  rw [hget] at hR
  obtain ⟨r1, rh, rw', r4, r5⟩ := hR
  have hgetq : st.roots[i]? = some (root, height, width) := by rw [List.getElem?_eq_getElem hil', hget]
  refine wp_then' (copyRoot_spec (ctx := env.ctx) (W := env.work) (i := i)
    (f := fun k ↦ if k < 4 then root.toList.getD k 0 else if k = 4 then height.toUInt64
      else width.toUInt64) (by reg_simp; exact h.rdi) (by reg_simp; exact (wd_zero _).symm)
    (by reg_simp; rw [hr9, shl6]) (fun k hk ↦ ?_)
    (fun k hk ↦ hL.work_not_ctxIn (by lay_omega) (by lay_omega))
    (fun k hk ↦ hL.dom _ (by lay_omega))) ?_
  · reg_simp
    simp only [Nat.toUInt64_eq] at *
    interval_cases k
    · simpa [getD_toList] using r1 0 (by omega)
    · simpa [getD_toList] using r1 1 (by omega)
    · simpa [getD_toList] using r1 2 (by omega)
    · simpa [getD_toList] using r1 3 (by omega)
    · simpa using r4
    · simpa using r5
  rintro s₅ ⟨h5, k5, r5'⟩ hs5
  have hdw := decodedWords_eq env.L
  have hpb := phaseBase_eq env.L p
  have hpl8 : env.proof.openings.length ≤ 8 := h.decoded.2.2.2.1
  have hW5 : ∀ k < workWords, s₅.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk ↦ k5 _ (hL.work_not_ctxIn (by lay_omega) hk)
  have hD5 : ∀ k < decodedWords env.L, s₅.mem (wd env.dec k) = s.mem (wd env.dec k) :=
    fun k hk ↦ k5 _ fun ⟨k', _, hk', e⟩ ↦ wd_ne_of_disj hL.fitDec hL.fitCtx hL.disjCD.symm hk
      (by lay_omega) e
  have K5 : Keep (Foot env) s.mem s₅.mem :=
    fun a ha ↦ k5 a fun hc ↦ ha (foot_ctx hc (by lay_omega) (by lay_omega))
  have hdW : ∀ k < decodedWords env.L, ∀ j < workWords, wd env.dec k ≠ wd env.work j :=
    fun k hk j hj ↦ wd_ne_of_disj hL.fitDec hL.fitWork hL.disjDW hk hj
  have hCW : ∀ k < ctxEnd, ∀ j < workWords, wd env.ctx k ≠ wd env.work j :=
    fun k hk j hj e ↦ hL.work_ne_ctx hj hk e.symm
  have e5 : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → s₅.reg r = s.reg r := fun r h1 h2 h3 ↦ by
    rw [r5' r (by simp [h1])]
    simp only [QState.setReg_reg, h1, h2, h3, ↓reduceIte]
  have hr8₅ : s₅.reg .r8 = env.work := by rw [r5' _ (by simp)]; reg_simp
  have hrdi₅ : s₅.reg .rdi = env.ctx := by rw [e5 _ (by simp) (by simp) (by simp)]; exact h.rdi
  have hr11₅ : s₅.reg .r11 = ps.length.toUInt64 := by rw [e5 _ (by simp) (by simp) (by simp)]; exact hr11
  refine wp_load (work_reg (env := env) hr8₅ _) (by rw [hW5 _ (by lay_omega)]; exact hpw) ?_
  refine wp_load (work_reg (env := env) (by reg_simp; exact hr8₅) _)
    (by reg_simp; rw [hW5 _ (by lay_omega)]; exact h.phaseCount) ?_
  by_cases hpc : p < env.proof.openings.length
  swap
  · refine wp_failIf_fail ?_ ⟨?_, by reg_simp; rw [hrdi₅, h.rdi], K5⟩
    · rw [cond_geu, rhs_reg]
      reg_simp
      exact decide_eq_true ((toUInt64_le (by omega) (by omega)).mpr (by omega))
    · unfold queryStep
      rw [hgetq, hop, List.drop_eq_nil_of_le (by omega)]
  refine wp_failIf (by
    rw [cond_geu, rhs_reg]
    reg_simp
    exact decide_eq_false fun e ↦ by rw [toUInt64_le (by omega) (by omega)] at e; omega) ?_
  refine wp_reg rfl (wp_store (work_reg (env := env) (by reg_simp; exact hr8₅) _)
    (by simp only [QState.setReg_mem]; rw [hs5]; exact hL.workSome _ (by lay_omega)) ?_)
  refine wp_gen fun s₆ hs₆ ↦ ?_
  have hW6 : ∀ k < workWords, k ≠ workPhase → s₆.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk hk' ↦ by rw [hs₆, setMem_wd_ne _ _ hk' (by lay_omega) (by lay_omega)]; exact hW5 k hk
  have hr8₆ : s₆.reg .r8 = env.work := by rw [hs₆]; reg_simp; exact hr8₅
  refine wp_load (work_reg (env := env) hr8₆ _) (by rw [hW6 _ (by lay_omega) (by lay_omega)]; exact hpp) ?_
  refine wp_reg rfl (wp_store (work_reg (env := env) (by reg_simp; exact hr8₆) _)
    (by
      simp only [QState.setReg_mem]
      rw [hs₆, isSome_setMem _ _ (by simp only [QState.setReg_mem]; rw [hs5]; exact hL.workSome _ (by lay_omega))]
      simp only [QState.setReg_mem]
      rw [hs5]
      exact hL.workSome _ (by lay_omega)) ?_)
  refine wp_gen fun s₇ hs₇ ↦ ?_
  have hpw7 : s₇.mem (wd env.work workPhase) = some (p + 1).toUInt64 := by
    rw [hs₇, hs₆]; mem_simp; rw [hpw, hr8₅] at *; rw [toUInt64_succ]
  have hpp7 : s₇.mem (wd env.work workPhasePtr) = some (wd env.dec (phaseBase env.L (p + 1))) := by
    rw [hs₇]; mem_simp; rw [eval_at]; reg_simp; rw [wdisp_toUInt64, wd_add, phaseBase_succ]
  have hW7 : ∀ k < workWords, k ≠ workPhase → k ≠ workPhasePtr →
      s₇.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk h1 h2 ↦ by rw [hs₇, setMem_wd_ne _ _ h2 (by lay_omega) (by lay_omega)]; exact hW6 k hk h1
  have hC7 : ∀ k < ctxEnd, s₇.mem (wd env.ctx k) = s₅.mem (wd env.ctx k) := fun k hk ↦ by
    rw [hs₇, hs₆]
    simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_of_not (hCW k hk _ (by lay_omega)), ite_of_not (hCW k hk _ (by lay_omega))]
  have hD7 : ∀ k < decodedWords env.L, s₇.mem (wd env.dec k) = s.mem (wd env.dec k) := fun k hk ↦ by
    rw [hs₇, hs₆]
    simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_of_not (hdW k hk _ (by lay_omega)), ite_of_not (hdW k hk _ (by lay_omega))]
    exact hD5 k hk
  have K7 : Keep (Foot env) s.mem s₇.mem := by
    rw [hs₇, hs₆]
    exact (K5.setMem (foot_work (by lay_omega)) _).setMem (foot_work (by lay_omega)) _
  have hs7 : ∀ a, (s₇.mem a).isSome = (s.mem a).isSome := fun a ↦ by
    rw [hs₇, hs₆]
    simp only [QState.setMem_mem, QState.setReg_mem]
    split
    · rename_i e; subst e; rw [hL.workSome _ (by lay_omega)]; rfl
    · split
      · rename_i e; subst e; rw [hL.workSome _ (by lay_omega)]; rfl
      · rw [hs5]; rfl
  have e7 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r13 → s₇.reg r = s₅.reg r := fun r h1 h2 h3 ↦ by
    rw [hs₇, hs₆]; simp only [QState.setMem_reg, QState.setReg_reg, h1, h2, h3, ↓reduceIte]
  have hr13₇ : s₇.reg .r13 = wd env.dec (phaseBase env.L p) := by rw [hs₇]; reg_simp
  obtain ⟨-, -, -, -, -, hph⟩ := h.decoded
  obtain ⟨ph, pw, hph32, hpw64, hq256, d0, d1, d2, hopn⟩ := hph p hpc
  have hph32' : ph ≤ 32 := hph32
  have hpw64' : pw ≤ 64 := hpw64
  have hq256' : env.proof.openings[p].length ≤ 256 := hq256
  have hgo : st.openings = env.proof.openings[p] :: env.proof.openings.drop (p + 1) := by
    rw [hop, List.drop_eq_getElem_cons hpc]
  refine wp_load (x := wd env.dec (phaseBase env.L p)) (by rw [eval_at0, hr13₇])
    (by rw [hD7 _ (by omega)]; exact d0) ?_
  have hr11₇ : s₇.reg .r11 = ps.length.toUInt64 := by
    rw [e7 _ (by simp) (by simp) (by simp)]; exact hr11₅
  have hrdi₇ : s₇.reg .rdi = env.ctx := by rw [e7 _ (by simp) (by simp) (by simp)]; exact hrdi₅
  by_cases hl : env.proof.openings[p].length = ps.length
  swap
  · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; reg_simp; rw [hr11₇]; exact toUInt64_ne (by omega) hn hl)
      ⟨by rw [queryStep_of hgetq hgo, openPhase_none_of_length hl]; rfl,
        by reg_simp; rw [hrdi₇, h.rdi], K7⟩
  refine wp_failIf (by rw [cond_ne, rhs_reg]; reg_simp; rw [hr11₇, hl]; exact bne_self_eq_false _) ?_
  refine wp_gen fun s₈ hs₈ ↦ ?_
  have hm8 : s₈.mem = s₇.mem := by rw [hs₈]; rfl
  have hr8 : ∀ r, r ≠ .rax → s₈.reg r = s₇.reg r := fun r hr ↦ by rw [hs₈]; reg_simp; simp [hr]
  refine wp_then (Q := fun s' ↦ s'.mem = s₈.mem ∧ RegsFrame [.rax, .rcx] s₈ s' ∧
    (ps.length ≠ 0 → ph = height ∧ pw = width)) ?_ ?_
  · by_cases hn0 : ps.length = 0
    · refine wp_ite_true (by rw [cond_eq, rhs_imm, hr8 _ (by simp), hr11₇, hn0]; rfl)
        (WP.skip ⟨rfl, rf_refl _ _, fun h ↦ absurd hn0 h⟩)
    have h0 : 0 < env.proof.openings[p].length := by omega
    refine wp_ite_false (by
      rw [cond_eq, rhs_imm, hr8 _ (by simp), hr11₇]
      exact beq_eq_false_iff_ne.mpr fun e ↦ hn0 ((toUInt64_inj hn (by norm_num)).mp e)) ?_
    have hrdi₈ : s₈.reg .rdi = env.ctx := by rw [hr8 _ (by simp)]; exact hrdi₇
    have hr13₈ : s₈.reg .r13 = wd env.dec (phaseBase env.L p) := by rw [hr8 _ (by simp)]; exact hr13₇
    refine wp_load (x := wd env.dec (phaseBase env.L p + 1)) (by rw [eval_at, hr13₈]; reg_simp; rw [add8_wd])
      (by rw [hm8, hD7 _ (by omega)]; exact d1) ?_
    refine wp_load (eval_cw (by reg_simp; exact hrdi₈) _)
      (by reg_simp; rw [hm8, hC7 _ (by lay_omega), h5 4 (by omega)]) ?_
    by_cases hh : ph = height
    swap
    · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; reg_simp; exact toUInt64_ne (by omega) rh hh)
        ⟨?_, by reg_simp; rw [hrdi₈, h.rdi], by simp only [QState.setReg_mem]; rw [hm8]; exact K7⟩
      rw [queryStep_of hgetq hgo, openPhase_none_of_shape ⟨_, List.getElem_mem h0,
        fun hs ↦ hh (by rw [← (hopn 0 h0).2.1]; exact hs.2)⟩]
      rfl
    refine wp_failIf (by rw [cond_ne, rhs_reg]; reg_simp; rw [hh]; exact bne_self_eq_false _) ?_
    refine wp_load (x := wd env.dec (phaseBase env.L p + 2)) (by rw [eval_at]; reg_simp; rw [hr13₈, add16_wd])
      (by reg_simp; rw [hm8, hD7 _ (by omega)]; exact d2) ?_
    refine wp_load (eval_cw (by reg_simp; exact hrdi₈) _)
      (by reg_simp; rw [hm8, hC7 _ (by lay_omega), h5 5 (by omega)]) ?_
    by_cases hw : pw = width
    swap
    · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; reg_simp; exact toUInt64_ne (by omega) rw' hw)
        ⟨?_, by reg_simp; rw [hrdi₈, h.rdi], by simp only [QState.setReg_mem]; rw [hm8]; exact K7⟩
      rw [queryStep_of hgetq hgo, openPhase_none_of_shape ⟨_, List.getElem_mem h0,
        fun hs ↦ hw (by rw [← (hopn 0 h0).1]; exact hs.1)⟩]
      rfl
    refine wp_failIf (by rw [cond_ne, rhs_reg]; reg_simp; rw [hw]; exact bne_self_eq_false _)
      (wp_done ⟨rfl, by rf_tac, fun _ ↦ ⟨hh, hw⟩⟩)
  rintro s₉ ⟨m9, r9', hsh⟩
  have hsim7 : SimState env { st with openings := env.proof.openings.drop (p + 1) } s₇ := by
    obtain ⟨c, hc, c1, c2⟩ := h.cursor
    refine SimState.mk' h hrdi₇ hs7 K7
      (h.sponge.congr fun k h1 h2 ↦ (hC7 _ (by lay_omega)).trans
        (k5.ctx (by lay_omega) (by lay_omega) (by lay_omega)))
      ⟨c, hc, by rw [hW7 _ (by lay_omega) (by lay_omega) (by lay_omega)]; exact c1, c2⟩
      ⟨p + 1, by omega, hpw7, hpp7, rfl⟩
      (by rw [hW7 _ (by lay_omega) (by lay_omega) (by lay_omega)]; exact h.phaseCount) h.rootsLen
      (by rw [hW7 _ (by lay_omega) (by lay_omega) (by lay_omega)]; exact h.rootCount) fun j hj ↦ ?_
    obtain ⟨q1, q2, q3, q4, q5⟩ := h.roots j hj
    have hj8 : j < 8 := lt_of_lt_of_le hj hrl
    exact ⟨fun k hk ↦ (hW7 _ (by lay_omega) (by lay_omega) (by lay_omega)).trans (q1 k hk), q2, q3,
      (hW7 _ (by lay_omega) (by lay_omega) (by lay_omega)).trans q4,
      (hW7 _ (by lay_omega) (by lay_omega) (by lay_omega)).trans q5⟩
  refine wp_reg rfl (wp_done ⟨root, height, width, p, hpc, hgetq, hop, hl, fun hn0 o ho ↦ ?_,
    hsim7.of_mem (by simp only [QState.setReg_mem]; rw [m9, hm8])
      (by reg_simp; rw [r9' _ (by simp), hr8 _ (by simp)]),
    fun k hk ↦ ?_, ?_, ?_, ?_, fun a ↦ ?_, fun a ha ↦ ?_, ?_⟩)
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
    exact ⟨by rw [(hopn j hj).1, (hsh hn0).2], by rw [(hopn j hj).2.1, (hsh hn0).1]⟩
  · simp only [QState.setReg_mem]
    rw [m9, hm8, hC7 _ (by lay_omega), h5 k (by omega)]
    simp [hk]
  · simp only [QState.setReg_mem]
    rw [m9, hm8, hC7 _ (by lay_omega), h5 4 (by omega)]
    rfl
  · simp only [QState.setReg_mem]
    rw [m9, hm8, hC7 _ (by lay_omega), h5 5 (by omega)]
    rfl
  · reg_simp
    rw [r9' _ (by simp), hr8 _ (by simp), hr13₇, add24_wd]
  · simp only [QState.setReg_mem]
    rw [m9, hm8]
    exact hs7 a
  · show s₉.mem a = s.mem a
    rw [m9, hm8]
    exact K7 a ha
  · rf_tac
    refine rf_back r9' (by simp) ?_
    subst hs₈
    rf_tac
    subst hs₇
    rf_tac
    subst hs₆
    rf_tac
    refine rf_back r5' (by simp) ?_
    rf_tac



end NativeVm.Transcript
