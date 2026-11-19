module

public import NativeVm.Code.Phase7.Chunk
public import NativeVm.Code.QueryRows
public import NativeVm.Transcript.QueryPre

/-!
# Phase 7: a level's query openings

`queryC` runs `queryOpenings k qs`: the level's index `k` from work word `cIdx`, the positions the
`WVec` at `queriesR`, the rows to `rowsR` (`Transcript.query`, `queryOpeningsM_spec`). Then the
opened root's width, a word of the transcript's roots table (`CodeRel.root`), goes to work word
`tmpO + 24`. Every row is that wide (`queryOpenings_rows`), so the rows are `RowsAt` of it
(`rowsAt_of_query`), and at most `wireMaxLeafWords = 64` wide (`queryOpenings_rows_le`). The query
writes the transcript's words and the rows only, both apart from the area's other words; a failed
one too, and the rows lie in the WHIR part's area, so the failure exit keeps `Fr`.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj Env Foot InArea Keeps ctxWork ctxEnd wdisp wd_inj wd_toNat
  wd_zero eval_cw eval_idx8 wp_load wp_store wp_reg toUInt64_shl workRoots rootStride)
open LeanVM.Protocol.Compile (wireMaxQueries wireMaxLeafWords)

/-! ## The model -/

/-- A query that returned kept the roots. -/
theorem qy_roots {t t' : TState} {i : Nat} {ps : Array UInt64} {rows : Array (Array UInt64)}
    (h : (Model.queryOpenings i ps).run t = some (rows, t')) : t'.roots = t.roots := by
  rw [Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph _ _
    cases ho : Model.openPhase r.digest r.height r.width ps ph with
    | none => rw [ho] at h; cases h
    | some rows' =>
      rw [ho] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl
  · cases h

/-! ## The rows' area -/

variable {p : Par} {t t' : TState} {s s' : QState}

theorem qy_rowsWords : rowsWords = 16384 := by decide

/-- The rows' words are the WHIR part's. -/
theorem qy_rows_mine {n : Nat} (hn : n ≤ rowsWords) {a : UInt64}
    (h : InArea (wd p.env.work rowsR.off) n a) : InMine p.env a := by
  obtain ⟨k, hk, rfl⟩ := h
  have := rows_off; have := qy_rowsWords; have := mineLo_val; have := dataEnd_eq
  exact ⟨rowsR.off + k, by omega, by omega, (wd_wd _ _ _)⟩

/-- An area word outside the rows' words is none of them. -/
theorem qy_not_rows {n j : Nat} (hn : n ≤ rowsWords) (hj : j < 2 ^ 61)
    (h : j < rowsR.off ∨ rowsR.off + rowsWords ≤ j) :
    ¬ InArea (wd p.env.work rowsR.off) n (wd p.env.work j) := by
  rintro ⟨k, hk, e⟩
  have := rows_off; have := qy_rowsWords
  rw [wd_wd] at e
  have := (wd_inj hj (by omega)).mp e
  omega

/-- A run with a new model state that keeps `Fr` keeps the invariant. -/
theorem qy_base (hb : Base p t s) (hr : CodeRel p.env t' s') (hf : Fr p.env s s') :
    Base p t' s' := by
  refine ⟨hr, hb.fr.trans hf, hb.inp.kept (rs := whirRegs) (kept_of_fr hf hb.rdi) ?_ hf.dom⟩
  intro r hr
  exact stop_le_of_mem (by simp only [whirRegs] at hr; simp only [regions]; simp_all) _

/-- The rows survive a write to another word of the area. -/
theorem qy_rows_keep {m m' : UInt64 → Option UInt64} {width : Nat} {rows : Array (Array UInt64)}
    (h : RowsAt m (wd p.env.work rowsR.off) width rows)
    (hm : ∀ j, j < rowsWords → m' (wd p.env.work (rowsR.off + j)) = m (wd p.env.work (rowsR.off + j))) :
    RowsAt m' (wd p.env.work rowsR.off) width rows := by
  refine ⟨h.1, fun i hi ↦ ⟨(h.2 i hi).1, fun j hj ↦ ?_⟩⟩
  have hw := (h.2 i hi).1
  have hlt : width * i + j < rowsWords := by
    have h1 : width * (i + 1) ≤ width * rows.size := Nat.mul_le_mul_left _ hi
    have h2 := h.1
    rw [Nat.mul_comm rows.size] at h2
    rw [Nat.mul_succ] at h1
    omega
  rw [wd_wd, wd_wd, hm _ hlt, ← wd_wd, ← wd_wd]
  exact (h.2 i hi).2 j hj

/-! ## The code -/

/-- After the query: the opened root's width to work word `tmpO + 24`. -/
def queryTail : List Stmt := [ldw .r9 cIdx, I (.shli .r9 6),
  I (.load .rax { base := .rbp, idx := some (.r9, .W8), disp := wdisp (workRoots + 5) }),
  stw (tmpO + 24) .rax]

/-- **A level's queries**: `queryOpenings k qs`, `k` at `cIdx`, `qs` at `queriesR`, the rows to
`rowsR`, the root's width to `tmpO + 24`. -/
def queryC : Stmt := blk (ldW :: ldw .r9 cIdx :: leaw .r10 (queriesR.off + 1) ::
  ldw .r11 queriesR.off :: leaw .r12 rowsR.off :: Transcript.query :: queryTail)

/-- The words `queryC` writes. -/
abbrev qyW : Nat → Prop := fun j ↦ rowsR.off ≤ j ∧ j < rowsR.off + rowsWords ∨ j = tmpO + 24

/-- The query, then the width, from the registers set. -/
theorem qy_tail {m0 : UInt64 → Option UInt64} {k : Nat} {qs : Array UInt64} (hk8 : k < 8)
    (hq1 : 1 ≤ qs.size) (hb : Base p t s) (hm0 : s.mem = m0)
    (hbp : s.reg .rbp = p.env.work) (h9 : s.reg .r9 = k.toUInt64)
    (h10 : s.reg .r10 = wd p.env.work (queriesR.off + 1)) (h11 : s.reg .r11 = qs.size.toUInt64)
    (h12 : s.reg .r12 = wd p.env.work rowsR.off) (hk : NatAt s.mem (wd p.env.work cIdx) k)
    (hq : WVec s.mem (wd p.env.work queriesR.off) queryCap qs) :
    WP (blk (Transcript.query :: queryTail)) s
      (fun s' ↦ ∃ rows t', (Model.queryOpenings k qs).run t = some (rows, t') ∧
        ∃ width, Base p t' s' ∧ RowsAt s'.mem (wd p.env.work rowsR.off) width rows ∧
          rows.size = qs.size ∧ width ≤ 64 ∧ NatAt s'.mem (wd p.env.work (tmpO + 24)) width ∧
          Only p.env qyW m0 s'.mem)
      (fun s' ↦ (Model.queryOpenings k qs).run t = none ∧ Err p s') := by
  have ro := rows_off; have qo := queries_off; have so := scratch_off; have ml := mineLo_val
  have de := dataEnd_eq; have rw' := qy_rowsWords
  have hww := workWords_ge p.inp.bytecode.size
  have hw69 := NativeVm.Transcript.workWords_val
  have qc : queryCap = 230 := rfl
  have wl : wireMaxLeafWords = 64 := rfl
  have wq : wireMaxQueries = 256 := rfl
  have hto : tmpO = scratchR.off + 32 := rfl
  have hci : cIdx = scratchR.off + 0 := rfl
  have hfw := hb.inp.fitWork
  obtain ⟨hqs, hcnt, hpos⟩ := hq
  have hn : qs.size * wireMaxLeafWords ≤ rowsWords := by rw [wl, rw']; omega
  have hpre : QueryPre p.env k qs (wd p.env.work (queriesR.off + 1))
      (wd p.env.work rowsR.off) s := {
    i_lt := by omega
    size_le := by omega
    r9 := h9
    r10 := h10
    r11 := h11
    r12 := h12
    pos := fun j hj ↦ by
      have := hpos j hj
      rw [wd_wd, wd_wd] at this
      rw [wd_wd, Nat.add_assoc]
      exact this
    fitPos := NativeVm.Transcript.Fits.sub hfw (by omega) (by omega)
    disjPosCtx := NativeVm.Transcript.Disj.sub hfw hb.inp.disjCtx.symm (by omega) (by omega)
    disjPosWork := by
      unfold Disj
      rw [wd_toNat hfw (by omega)]
      omega
    fitRows := NativeVm.Transcript.Fits.sub hfw (by omega) (by omega)
    rowsSome := fun j hj ↦ by
      rw [wd_wd]
      exact hb.inp.workSome _ (by omega)
    disjRowsCtx := NativeVm.Transcript.Disj.sub hfw hb.inp.disjCtx.symm (by omega) (by omega)
    disjRowsDec := NativeVm.Transcript.Disj.sub hfw hb.inp.disjDec.symm (by omega) (by omega)
    disjRowsWork := by
      unfold Disj
      rw [wd_toNat hfw (by omega)]
      omega
    disjRowsPos := by
      unfold Disj
      rw [wd_toNat hfw (by omega), wd_toNat hfw (by omega)]
      omega }
  apply WP.blk_cons
  refine WP.mono (NativeVm.Transcript.WP.frame (queryOpeningsM_spec hb.rel hpre)) ?_ ?_
  · rintro s1 ⟨⟨rows, t', hrun, hc, hrows, hkp⟩, hd, -⟩
    have hf : Fr p.env s s1 := ⟨hkp.rdi, hd, fun a ha hmine ↦ hkp.mem a fun h ↦
      h.elim ha fun h' ↦ hmine (qy_rows_mine hn h')⟩
    have hb1 := qy_base hb hc hf
    have hm1 : ∀ j, mineLo ≤ j → j < dataEnd → (j < rowsR.off ∨ rowsR.off + rowsWords ≤ j) →
        s1.mem (wd p.env.work j) = s.mem (wd p.env.work j) := fun j h1 h2 h3 ↦
      hkp.mem _ fun h ↦ h.elim (InMine.not_foot hb.inp (inMine_wd h1 h2))
        (qy_not_rows hn (by omega) h3)
    obtain ⟨r, hr, hsz, hw⟩ := queryOpenings_rows hrun
    have hle := queryOpenings_rows_le hb.rel hrun
    have hwid : r.width ≤ 64 := by
      have := hle 0 (by omega)
      rw [hw 0 (by omega)] at this
      exact this
    obtain ⟨hkr, hrk⟩ := Array.getElem?_eq_some_iff.mp hr
    have hk' : k < t'.roots.size := by rw [qy_roots hrun]; exact hkr
    have hra := hc.root hk'
    have hrt : t'.roots[k] = r := by
      rw [← hrk]
      congr 1
      exact qy_roots hrun
    rw [hrt] at hra
    obtain ⟨-, -, hwlt, -, hwd⟩ := hra
    have hbp1 : s1.reg .rbp = p.env.work := by
      rw [hkp.regs .rbp (by decide)]; exact hbp
    unfold queryTail ldw stw
    refine wp_load (eval_w hbp1 cIdx) (by rw [hm1 cIdx (by omega) (by omega) (by omega)]; exact hk.2) ?_
    refine wp_reg rfl ?_
    refine wp_load (eval_idx8 (j := 0) (i := 8 * k) (by rsimp; rw [hbp1, wd_zero]) ?_ _)
      (show s1.mem _ = _ by
        rw [show 0 + 8 * k + (workRoots + 5) = workRoots + rootStride * k + 5 by
          rw [NativeVm.Transcript.workRoots_val, NativeVm.Transcript.rootStride_val]; omega]
        exact hwd) ?_
    · rsimp
      rw [show (6 : UInt64) = (6 : Nat).toUInt64 from rfl, toUInt64_shl k 6 (by omega)]
      congr 1
      omega
    have hsome : (s1.mem (wd p.env.work (tmpO + 24))).isSome := hb1.some (by omega) (by omega)
    refine wp_store (eval_w (by rsimp; exact hbp1) _) (by rsimp; exact hsome) ?_
    refine WP.blk_nil ⟨rows, t', hrun, r.width, ?_, ?_, hsz, hwid, ⟨hwlt, ?_⟩, ?_⟩
    · refine hb1.frM (frM_of (W' := fun j ↦ j = tmpO + 24) (by rsimp) (fun a ↦ ?_) (fun a ha ↦ ?_)
        (fun j hj ↦ by subst hj; omega))
      · rw [NativeVm.Transcript.isSome_setMem _ _ (by rsimp; exact hsome)]
        rfl
      · rw [QState.setMem_mem, ite_eq_right (ha _ rfl)]
        rfl
    · have hbd : rows.size * r.width ≤ rowsWords := by
        rw [hsz]
        exact le_trans (Nat.mul_le_mul (show qs.size ≤ 230 by omega) hwid) (by rw [rw']; decide)
      refine qy_rows_keep (rowsAt_of_query hrows hw hbd) fun j hj ↦ ?_
      have ne : wd p.env.work (rowsR.off + j) ≠ wd p.env.work (tmpO + 24) := fun e ↦ by
        have := (wd_inj (by omega) (by omega)).mp e; omega
      rw [QState.setMem_mem, ite_eq_right ne]
      rfl
    · rw [QState.setMem_mem, ite_eq_left rfl]
      rsimp
      rfl
    · intro j h1 h2 hj
      have ne : wd p.env.work j ≠ wd p.env.work (tmpO + 24) := fun e ↦ by
        have := (wd_inj (by omega) (by omega)).mp e; exact hj (.inr this)
      rw [QState.setMem_mem, ite_eq_right ne]
      show s1.mem _ = _
      rw [← hm0]
      exact hm1 j h1 h2 (by omega)
  · rintro s1 ⟨⟨hrun, hrdi, hke⟩, hd, -⟩
    exact ⟨hrun, hb.fr.trans ⟨hrdi, hd, fun a ha hmine ↦ hke a ha fun h' ↦
      hmine (qy_rows_mine hn h')⟩⟩

/-- **`queryC` opens a level's queries.** -/
theorem queryC_spec {p : Par} {m0 : UInt64 → Option UInt64} {k : Nat} {qs : Array UInt64}
    (hk : k < 8) (hq1 : 1 ≤ qs.size) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cIdx) k ∧
        WVec s.mem (wd p.env.work queriesR.off) queryCap qs)
      queryC (queryOpenings k qs)
      (fun rows t s ↦ ∃ width, Base p t s ∧ RowsAt s.mem (wd p.env.work rowsR.off) width rows ∧
        rows.size = qs.size ∧ width ≤ 64 ∧ NatAt s.mem (wd p.env.work (tmpO + 24)) width ∧
        Only p.env (fun j ↦ rowsR.off ≤ j ∧ j < rowsR.off + rowsWords ∨ j = tmpO + 24) m0 s.mem)
      (Err p) := by
  rintro t s ⟨hb, hm, hki, hq⟩
  unfold queryC ldW ldw leaw
  refine wp_load (eval_cw hb.rdi ctxWork) hb.workPtr ?_
  have hW : (s.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
  refine wp_load (eval_w hW cIdx) (by rsimp; exact hki.2) ?_
  refine wp_reg rfl ?_
  refine wp_load (eval_w (env := p.env) (by rsimp) queriesR.off) (by rsimp; exact hq.2.1.2) ?_
  refine wp_reg rfl ?_
  refine qy_tail hk hq1 (hb.frM ⟨by rsimp, fun _ ↦ rfl, fun _ _ ↦ rfl⟩) hm (by rsimp) (by rsimp)
    ?_ (by rsimp) ?_ hki hq
  · rsimp
    exact eval_w (env := p.env) (by rsimp) _
  · rsimp
    exact eval_w (env := p.env) (by rsimp) _

end NativeVm.Code.P7
