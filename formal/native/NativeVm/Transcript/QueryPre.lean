module

public import NativeVm.Transcript.QueryOne

/-!
# A query's prelude

What `query` does before its openings: root `i` and its shape into the context's `qRootW` words
(`copyRoot_spec`), the next phase taken (its index and address advanced), its query count checked
against the positions' and, when it has queries, its shape against the root's (`queryHead_spec`).
Also the facts the openings' loop needs: sub-areas (`Fits.sub`, `Disj.sub`), the rows' words
(`rowsAt_of`) and the relation kept by writes outside its words (`SimState.congrW`).
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

variable {env : Env} {st : VerifierProgramState} {s : QState} {E : QState → Prop}

/-! ## Areas -/

theorem Fits.sub {b : UInt64} {N k m : Nat} (h : Fits b N) (hk : k < N) (hkm : k + m ≤ N) :
    Fits (wd b k) m := by
  have := wd_toNat h hk
  unfold Fits at *
  omega

theorem Disj.sub {b c : UInt64} {N M k m : Nat} (hb : Fits b N) (h : Disj b N c M) (hk : k < N)
    (hkm : k + m ≤ N) : Disj (wd b k) m c M := by
  have := wd_toNat hb hk
  unfold Disj at *
  omega

/-! ## The rows -/

theorem rowsAt_of {mem : UInt64 → Option UInt64} {w : Nat} : ∀ {b : UInt64} {rows : List (List K)},
    (∀ r ∈ rows, r.length = w) →
    (∀ k (hk : k < rows.length), ∀ t < w, mem (wd b (k * w + t)) = some (rows[k].getD t 0).lane) →
    QueryRowsAt mem b rows
  | _, [], _, _ => fun i h ↦ absurd h (by simp)
  | b, r :: rs, hl, hw => by
    have hr : r.length = w := hl r (by simp)
    have ih := rowsAt_of (b := wd b w) (rows := rs) (fun r' h' ↦ hl r' (by simp [h']))
      (fun k hk t ht ↦ by
        rw [wd_shift, show w + (k * w + t) = (k + 1) * w + t by rw [Nat.add_mul]; omega]
        exact hw (k + 1) (by simpa using hk) t ht)
    intro i hi
    simp only [List.flatten_cons, List.length_append] at hi
    simp only [List.flatten_cons]
    by_cases hiw : i < r.length
    · rw [List.getElem_append_left hiw]
      have := hw 0 (by simp) i (by omega)
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero] at this
      rw [this, List.getD_eq_getElem _ _ hiw]
    · rw [List.getElem_append_right (by omega)]
      have := ih (i - r.length) (by omega)
      rw [wd_shift, show w + (i - r.length) = i by omega] at this
      exact this

/-! ## The relation kept -/

/-- **`SimState` through writes outside its words**: the context's below the scratch area and the
sponge's, the decoded proof's and the working area's kept. -/
theorem SimState.congrW {s' : QState} (h : SimState env st s) (hrdi : s'.reg .rdi = env.ctx)
    (hs : ∀ a, (s'.mem a).isSome = (s.mem a).isSome)
    (hctx : ∀ k, k < scratchW ∨ (laneW ≤ k ∧ k < groundW + 3) →
      s'.mem (wd env.ctx k) = s.mem (wd env.ctx k))
    (hdec : ∀ k < decodedWords env.L, s'.mem (wd env.dec k) = s.mem (wd env.dec k))
    (hwork : ∀ k < workWords, s'.mem (wd env.work k) = s.mem (wd env.work k)) :
    SimState env st s' := by
  have hL := h.layout
  obtain ⟨c, hc, c1, c2⟩ := h.cursor
  obtain ⟨p, hp, p1, p2, p3⟩ := h.phase
  have hrl := h.rootsLen
  simp only [maxRoots_val] at hrl
  exact {
    rdi := hrdi
    layout := ⟨hL.fitCtx, hL.fitDec, hL.fitWork, hL.disjCD, hL.disjCW, hL.disjDW,
      fun k hk ↦ by rw [hs]; exact hL.ctxSome k hk, fun k hk ↦ by rw [hs]; exact hL.workSome k hk,
      by rw [hctx _ (.inl (by lay_omega))]; exact hL.decPtr,
      by rw [hctx _ (.inl (by lay_omega))]; exact hL.workPtr⟩
    decoded := Decoded.congr h.decoded hdec
    sponge := h.sponge.congr fun k h1 h2 ↦ hctx k (.inr ⟨h1, h2⟩)
    cursor := ⟨c, hc, by rw [hwork _ (by lay_omega)]; exact c1, c2⟩
    phase := ⟨p, hp, by rw [hwork _ (by lay_omega)]; exact p1, by rw [hwork _ (by lay_omega)]; exact p2, p3⟩
    phaseCount := by rw [hwork _ (by lay_omega)]; exact h.phaseCount
    rootsLen := h.rootsLen
    rootCount := by rw [hwork _ (by lay_omega)]; exact h.rootCount
    roots := fun j hj ↦ by
      obtain ⟨r1, r2, r3, r4, r5⟩ := h.roots j hj
      refine ⟨fun k hk ↦ ?_, r2, r3, ?_, ?_⟩
      · rw [hwork _ (by lay_omega)]; exact r1 k hk
      · rw [hwork _ (by lay_omega)]; exact r4
      · rw [hwork _ (by lay_omega)]; exact r5 }

/-! ## The root -/

/-- Copy word `k` of the root entry at `r8 + r9` to the context's `qRootW + k`. -/
def rootP (k : Nat) : List Stmt :=
  [I (.load .rax { base := .r8, idx := some (.r9, .W8), disp := wdisp (workRoots + k) }),
    I (.store (cw (qRootW + k)) .rax)]

/-- **Root `i`'s entry** into the context's `qRootW` words. -/
theorem copyRoot_spec {ctx W : UInt64} {i : Nat} {f : Nat → UInt64} (hrdi : s.reg .rdi = ctx)
    (hr8 : s.reg .r8 = wd W 0) (hr9 : s.reg .r9 = (8 * (8 * i)).toUInt64)
    (hv : ∀ k < 6, s.mem (wd W (rootW i k)) = some (f k))
    (hne : ∀ k < 6, ¬ CtxIn ctx qRootW (qRootW + 6) (wd W (rootW i k)))
    (hd : ∀ k < 6, (s.mem (wd ctx (qRootW + k))).isSome) :
    WP (blk ((List.range 6).flatMap rootP)) s (fun s' ↦
      (∀ k < 6, s'.mem (wd ctx (qRootW + k)) = some (f k)) ∧
      Keep (CtxIn ctx qRootW (qRootW + 6)) s.mem s'.mem ∧ RegsFrame [.rax] s s') E := by
  refine Keccak.Proof.wp_range_flatMap (s := s) _ (fun j s' ↦ (∀ t < j, s'.mem (wd ctx (qRootW + t)) =
    some (f t)) ∧ Keep (CtxIn ctx qRootW (qRootW + j)) s.mem s'.mem ∧ RegsFrame [.rax] s s') 6 ?_
    ⟨fun t ht ↦ absurd ht (by omega), Keep.refl _ _, rf_refl _ _⟩
  intro j hj s' ⟨hw, hk, hr⟩
  have hrdi' : s'.reg .rdi = ctx := (hr _ (by simp)).trans hrdi
  have ha : ({ base := .r8, idx := some (.r9, .W8), disp := wdisp (workRoots + j) } : Addr).eval s' =
      wd W (rootW i j) := by
    rw [eval_idx8 ((hr _ (by simp)).trans hr8) ((hr _ (by simp)).trans hr9)]
    congr 1
    simp only [rootW, rootStride_val]
    omega
  refine wp_load ha (by rw [hk _ fun h ↦ hne j hj (h.mono le_rfl (by omega))]; exact hv j hj)
    (wp_store (eval_cw (by reg_simp; exact hrdi') _) ?_ (wp_done ⟨?_, ?_, ?_⟩))
  · rw [QState.setReg_mem, hk.ctx (by omega) (by lay_omega) (by lay_omega)]
    exact hd j hj
  · intro t ht
    simp only [QState.setMem_mem, QState.setReg_mem, QState.setReg_reg, ↓reduceIte]
    split
    · rename_i e
      rw [wd_inj (by lay_omega) (by lay_omega)] at e
      rw [show t = j by omega]
    · rename_i e
      rw [wd_inj (by lay_omega) (by lay_omega)] at e
      exact hw t (by omega)
  · exact Keep.update (hk.mono fun a ha ↦ ha.mono le_rfl (by omega)) (CtxIn.word (by omega)
      (by omega)) _
  · exact rf_setMem (rf_setReg hr (by simp) _) _ _

end NativeVm.Transcript
