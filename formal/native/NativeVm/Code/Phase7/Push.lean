module

public import NativeVm.Code.Phase7.Chunk

/-!
# A fold round's bookkeeping

`pushC`: `α` (temporary pair `8`) appended to WHIR's `α`s, `(α, β)` (pairs `8`, `10`) to the level's
rounds; the stores at indexed addresses (`ix`), the index the arrays' counts.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw eval_idx64 wp_load wp_store wp_reg
  isSome_setMem ctxWork toUInt64_shl toUInt64_succ)

/-- The area's word `k` past the index `r` (in words). -/
def ix (r : Reg64) (k : Nat) : Addr := { base := .rbp, idx := some (r, .W64), disp := wdisp k }

/-- Append `α` to WHIR's `α`s and `(α, β)` to the rounds. -/
def pushC : Stmt := blk [ldW,
  ldw .rax (whirR.off + 2), I (.mov .rcx .rax), I (.shli .rcx 1),
  ldw .r9 (tmpO + 8), ldw .r10 (tmpO + 9),
  I (.store (ix .rcx (whirR.off + 3)) .r9), I (.store (ix .rcx (whirR.off + 4)) .r10),
  I (.addi .rax 1), stw (whirR.off + 2) .rax,
  ldw .rax roundsR.off, I (.mov .rcx .rax), I (.shli .rcx 2),
  I (.store (ix .rcx (roundsR.off + 1)) .r9), I (.store (ix .rcx (roundsR.off + 2)) .r10),
  ldw .r9 (tmpO + 10), ldw .r10 (tmpO + 11),
  I (.store (ix .rcx (roundsR.off + 3)) .r9), I (.store (ix .rcx (roundsR.off + 4)) .r10),
  I (.addi .rax 1), stw roundsR.off .rax]

/-- The words `pushC` writes. -/
def pushWritten (k : Nat) : Prop :=
  (whirR.off + 2 ≤ k ∧ k < whirR.off + whirGluedOff) ∨ (roundsR.off ≤ k ∧ k < roundsR.off + roundsWords)

theorem eval_ix {s : QState} {W : UInt64} {r : Reg64} {i : Nat} (hW : s.reg .rbp = W)
    (hr : s.reg r = i.toUInt64) (k : Nat) : (ix r k).eval s = wd W (i + k) := by
  have := eval_idx64 (s := s) (base := .rbp) (ix := r) (b := W) (j := 0) (by rw [hW, wd_zero]) hr k
  rwa [Nat.zero_add] at this

theorem shl_toUInt64 (c n : Nat) (hn : n < 64) : c.toUInt64 <<< (n.toUInt64) = (2 ^ n * c).toUInt64 :=
  toUInt64_shl c n hn

variable {env : Env} {s : QState} {F : QState → Prop}

theorem stix_wp {rest : List Stmt} {P : QState → Prop} {W : UInt64} {r src : Reg64} {i k : Nat}
    (hW : s.reg .rbp = W) (hr : s.reg r = i.toUInt64) (hk : (s.mem (wd W (i + k))).isSome)
    (h : WP (blk rest) (s.setMem (wd W (i + k)) (s.reg src)) P F) :
    WP (blk (I (.store (ix r k) src) :: rest)) s P F :=
  wp_store (eval_ix hW hr k) hk h


theorem natAt_val {mem : UInt64 → Option UInt64} {a : UInt64} {n : Nat} (h : NatAt mem a n) :
    mem a = some n.toUInt64 := h.2

/-- **`pushC`**. -/
theorem pushC_core {sW : WhirStateW} {rs : Array FoldRoundW} {alpha beta : EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hsome : ∀ k, pushWritten k → (s.mem (wd env.work k)).isSome)
    (hw : WhirAt s.mem (whirR.at env.work) sW) (hr : RoundsAt s.mem (roundsR.at env.work) rs)
    (ha : EWAt s.mem (wd env.work (tmpO + 8)) alpha) (hb : EWAt s.mem (wd env.work (tmpO + 10)) beta)
    (hα : sW.alphas.size < stackCap) (hrs : rs.size < roundCap) :
    WP pushC s (fun s' ↦ WhirAt s'.mem (whirR.at env.work) { sW with alphas := sW.alphas.push alpha } ∧
      RoundsAt s'.mem (roundsR.at env.work) (rs.push ⟨alpha, beta⟩) ∧
      (∀ a, (∀ k, pushWritten k → a ≠ wd env.work k) → s'.mem a = s.mem a)) F := by
  obtain ⟨hc, ⟨hasz, hn, hal⟩, hgsz, hgn, hg⟩ := hw
  obtain ⟨hrsz, hrn, hrr⟩ := hr
  have hn30 : sW.alphas.size < 30 := hα
  have hm6 : rs.size < 6 := hrs
  have wo := whir_off; have ro := rounds_off
  simp only [Region.at, wd_wd] at hn hrn hal hrr hc hgn hg
  obtain ⟨a0, a1⟩ := ewat_wd ha
  obtain ⟨b0, b1⟩ := ewat_wd hb
  unfold pushC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := env) (by wsimp) (by wsimp; exact hn.2) ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine ldw_wp (env := env) (by wsimp) (by wsimp; exact a0) ?_
  refine ldw_wp (env := env) (by wsimp) (by wsimp; exact a1) ?_
  have e2n : sW.alphas.size.toUInt64 <<< (1 : Nat).toUInt64 = (2 * sW.alphas.size).toUInt64 := by
    rw [shl_toUInt64 sW.alphas.size 1 (by omega), pow_one]
  refine stix_wp (W := env.work) (i := 2 * sW.alphas.size) (by wsimp) (by wsimp; exact e2n)
    (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine stix_wp (W := env.work) (i := 2 * sW.alphas.size) (by wsimp) (by wsimp; exact e2n)
    (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := env) (by wsimp) (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine ldw_wp (env := env) (by wsimp) (by wsimp; exact hrn.2) ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  have e4m : rs.size.toUInt64 <<< (2 : Nat).toUInt64 = (4 * rs.size).toUInt64 := by
    rw [shl_toUInt64 rs.size 2 (by omega)]; rfl
  refine stix_wp (W := env.work) (i := 4 * rs.size) (by wsimp) (by wsimp; exact e4m)
    (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine stix_wp (W := env.work) (i := 4 * rs.size) (by wsimp) (by wsimp; exact e4m)
    (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine ldw_wp (env := env) (by wsimp) (by wsimp; exact b0) ?_
  refine ldw_wp (env := env) (by wsimp) (by wsimp; exact b1) ?_
  refine stix_wp (W := env.work) (i := 4 * rs.size) (by wsimp) (by wsimp; exact e4m)
    (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine stix_wp (W := env.work) (i := 4 * rs.size) (by wsimp) (by wsimp; exact e4m)
    (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := env) (by wsimp) (by wsimp; exact hsome _ (by unfold pushWritten; oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  have hU : ∀ k, ¬ (k = whirR.off + 2 ∨ k = 2 * sW.alphas.size + (whirR.off + 3) ∨
      k = 2 * sW.alphas.size + (whirR.off + 4) ∨ k = roundsR.off ∨
      (4 * rs.size + (roundsR.off + 1) ≤ k ∧ k ≤ 4 * rs.size + (roundsR.off + 4))) → k < 2 ^ 61 →
      s'.mem (wd env.work k) = s.mem (wd env.work k) := by
    intro k hk hk'
    rw [← hs']
    wsimp
  have c1 : s'.mem (wd env.work (whirR.off + 2)) = some (sW.alphas.size + 1).toUInt64 := by
    rw [← hs']; wsimp; rw [← toUInt64_succ]; rfl
  have c2 : s'.mem (wd env.work roundsR.off) = some (rs.size + 1).toUInt64 := by
    rw [← hs']; wsimp; rw [← toUInt64_succ]; rfl
  have v0 : s'.mem (wd env.work (2 * sW.alphas.size + (whirR.off + 3))) = some alpha.c0 := by rw [← hs']; wsimp
  have v1 : s'.mem (wd env.work (2 * sW.alphas.size + (whirR.off + 4))) = some alpha.c1 := by rw [← hs']; wsimp
  have w1 : s'.mem (wd env.work (4 * rs.size + (roundsR.off + 1))) = some alpha.c0 := by rw [← hs']; wsimp
  have w2 : s'.mem (wd env.work (4 * rs.size + (roundsR.off + 2))) = some alpha.c1 := by rw [← hs']; wsimp
  have w3 : s'.mem (wd env.work (4 * rs.size + (roundsR.off + 3))) = some beta.c0 := by rw [← hs']; wsimp
  have w4 : s'.mem (wd env.work (4 * rs.size + (roundsR.off + 4))) = some beta.c1 := by rw [← hs']; wsimp
  have sm : ∀ o len, (∀ j < len, ¬ (o + j = whirR.off + 2 ∨ o + j = 2 * sW.alphas.size + (whirR.off + 3) ∨
      o + j = 2 * sW.alphas.size + (whirR.off + 4) ∨ o + j = roundsR.off ∨
      (4 * rs.size + (roundsR.off + 1) ≤ o + j ∧ o + j ≤ 4 * rs.size + (roundsR.off + 4))) ∧
      o + j < 2 ^ 61) →
      Same s.mem s'.mem (wd env.work o) len := fun o len h j hj ↦ by
    rw [wd_wd]; exact hU _ (h j hj).1 (h j hj).2
  refine ⟨⟨?_, ?_, hgsz, ?_, ?_⟩, ?_, ?_⟩
  · exact hc.congr (sm _ _ fun j hj ↦ ⟨by oomega, by oomega⟩)
  · have hev : EVec s.mem (wd (wd env.work whirR.off) 2) stackCap sW.alphas :=
      ⟨hasz, by rw [wd_wd]; exact hn, by rw [wd_wd, wd_wd]; exact hal⟩
    refine EVec.push hev ?_ ?_ ?_ hα
    · simp only [Region.at, wd_wd]
      exact sm _ _ fun j hj ↦ ⟨by oomega, by oomega⟩
    · simp only [Region.at, wd_wd]; exact ⟨by omega, c1⟩
    · simp only [Region.at, wd_wd]
      refine ⟨?_, ?_⟩
      · rw [show whirR.off + 2 + (1 + 2 * sW.alphas.size) = 2 * sW.alphas.size + (whirR.off + 3) by omega]; exact v0
      · rw [wd_wd, show whirR.off + 2 + (1 + 2 * sW.alphas.size) + 1 = 2 * sW.alphas.size + (whirR.off + 4) by omega]
        exact v1
  · show NatAt s'.mem (wd (wd env.work whirR.off) whirGluedOff) sW.glued.size
    simp only [wd_wd]
    exact hgn.congr (hU _ (by oomega) (by oomega))
  · intro i hi
    show GluedAt s'.mem (wd (wd env.work whirR.off) (whirGluedOff + 1 + gluedWords * i)) sW.glued[i]
    change i < sW.glued.size at hi
    have hi' : i < 10 := by have := hgsz; rw [gluedCap_val] at this; omega
    simp only [wd_wd]
    refine (hg i hi).congr (sm _ _ fun j hj ↦ ⟨by oomega, by oomega⟩)
  · refine RoundsAt.push ⟨hrsz, by rw [Region.at]; exact hrn, fun i hi ↦ ?_⟩ ?_ ?_ ?_ ?_ hrs
    · simp only [Region.at, wd_wd]; exact hrr i hi
    · simp only [Region.at, wd_wd]
      exact sm _ _ fun j hj ↦ ⟨by oomega, by oomega⟩
    · simp only [Region.at]; exact ⟨by omega, c2⟩
    · simp only [Region.at, wd_wd]
      refine ⟨?_, ?_⟩
      · rw [show roundsR.off + (1 + 4 * rs.size) = 4 * rs.size + (roundsR.off + 1) by omega]; exact w1
      · rw [wd_wd, show roundsR.off + (1 + 4 * rs.size) + 1 = 4 * rs.size + (roundsR.off + 2) by omega]; exact w2
    · simp only [Region.at, wd_wd]
      refine ⟨?_, ?_⟩
      · rw [show roundsR.off + (3 + 4 * rs.size) = 4 * rs.size + (roundsR.off + 3) by omega]; exact w3
      · rw [wd_wd, show roundsR.off + (3 + 4 * rs.size) + 1 = 4 * rs.size + (roundsR.off + 4) by omega]; exact w4
  · intro a ha
    rw [← hs']
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    all_goals exact ha _ (by unfold pushWritten; oomega)

/-- **`pushC`**, with its frame. -/
theorem pushC_spec {sW : WhirStateW} {rs : Array FoldRoundW} {alpha beta : EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hsome : ∀ k, pushWritten k → (s.mem (wd env.work k)).isSome)
    (hw : WhirAt s.mem (whirR.at env.work) sW) (hr : RoundsAt s.mem (roundsR.at env.work) rs)
    (ha : EWAt s.mem (wd env.work (tmpO + 8)) alpha) (hb : EWAt s.mem (wd env.work (tmpO + 10)) beta)
    (hα : sW.alphas.size < stackCap) (hrs : rs.size < roundCap) :
    WP pushC s (fun s' ↦ WhirAt s'.mem (whirR.at env.work) { sW with alphas := sW.alphas.push alpha } ∧
      RoundsAt s'.mem (roundsR.at env.work) (rs.push ⟨alpha, beta⟩) ∧
      (∀ a, (∀ k, pushWritten k → a ≠ wd env.work k) → s'.mem a = s.mem a) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
      (∀ r, r ∉ [.rax, .rcx, .r9, .r10, .rbp] → s'.reg r = s.reg r)) F :=
  WP.mono (NativeVm.Transcript.WP.frame (pushC_core hrdi hwp hsome hw hr ha hb hα hrs))
    (fun _ ⟨⟨h1, h2, h3⟩, hd, hreg⟩ ↦ ⟨h1, h2, h3, hd, fun r hr ↦ hreg r (by
      revert hr; cases r <;> decide)⟩) fun _ h ↦ h.1

end NativeVm.Code.P7
