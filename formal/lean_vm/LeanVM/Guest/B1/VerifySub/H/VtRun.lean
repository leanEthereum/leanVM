/-
  LeanVM.Guest.B1.VerifySub.H.VtRun

  An accepting run of `tablesSeg` on a claimed evaluator, read back: the words it reads, phase by
  phase, the claim at the bytecode share's point and value, and the sponge it ends on.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AHon
public import LeanVM.Guest.B1.Tables.Vt.AsmForms

/-!
# `tablesSeg`, read back

`runsG_total`: a run of a program that runs on every `k` words reads `k` words and leaves no
ground challenge. `runsG_readE_inv`, `runsG_readN_inv`, `runsG_require_inv'`: the reads and the
requirements of a run. `chunks`, `tableTerms_any`: the table loop runs on every `153` words.

`vt_inv`: an accepting run of `tablesSeg` on `claimedBytecodeValue cl` from a carried capacity,
over the layout of six row counts, reads four framework words, the bytecode share's ten, the
table sumcheck's `3 n` and the tables' `153` evaluations; the claim is the share's point and
value (`BytecodeAt`), and the run ends on a squeeze, nothing waiting.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs read back -/

/-- **A run reads the words every run reads**, and ends with no ground challenge. -/
theorem runsG_total {α : Type} {p : VerifierProgram α} {s t : Fs} {g : Option E} {xs : List E}
    {a : α} (h : RunsG p s none xs a t g) (hc : ∃ sp, s.Carries sp) {k : ℕ}
    (hall : ∀ ys : List E, ys.length = k → ∃ (b : α) (u : Fs), RunsTo p s ys b u) :
    xs.length = k ∧ g = none := by
  obtain ⟨b, u, hb⟩ := hall ((xs ++ List.replicate k 0).take k) (by simp)
  obtain ⟨-, -, -, hr⟩ := RunsG.det h (RunsTo.toG hb) hc (r1 := List.replicate k 0)
    (r2 := (xs ++ List.replicate k 0).drop k) (List.take_append_drop _ _).symm
  have hl := congrArg List.length hr
  simp only [List.length_replicate, List.length_drop, List.length_append] at hl
  have hk : xs.length = k := by omega
  obtain ⟨b', u', hb'⟩ := hall xs hk
  obtain ⟨-, -, eg, -⟩ := RunsG.det h (RunsTo.toG hb') hc (r1 := []) (r2 := []) rfl
  exact ⟨hk, eg⟩

/-- A run on the words a known run reads is that run. -/
theorem runsG_on {α : Type} {p : VerifierProgram α} {s t u : Fs} {g : Option E} {xs : List E}
    {a b : α} (h : RunsG p s none xs a t g) (h' : RunsTo p s xs b u) (hc : ∃ sp, s.Carries sp) :
    a = b ∧ t = u ∧ g = none := by
  obtain ⟨e1, e2, e3, -⟩ := RunsG.det h (RunsTo.toG h') hc (r1 := []) (r2 := []) rfl
  exact ⟨e1, e2, e3⟩

theorem runsG_readE_inv {s t : Fs} {g : Option E} {xs : List E} {a : E}
    (h : RunsG VerifierProgram.readScalar s none xs a t g) (hc : ∃ sp, s.Carries sp) :
    xs = [a] ∧ t = s.absorb a dsObserve ∧ g = none := by
  obtain ⟨hl, -⟩ := runsG_total h hc (k := 1) fun ys hy ↦ by
    match ys, hy with
    | [y], _ => exact ⟨y, _, runsTo_readE s y⟩
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨rfl, rfl, rfl⟩ := runsG_on h (runsTo_readE s y) hc
  exact ⟨rfl, rfl, rfl⟩

theorem runsG_readN_inv {n : ℕ} {s t : Fs} {g : Option E} {xs a : List E}
    (h : RunsG (VerifierProgram.readScalars n) s none xs a t g) (hc : ∃ sp, s.Carries sp) :
    xs = a ∧ a.length = n ∧ t = s.absorbAll a dsObserve ∧ g = none := by
  obtain ⟨hl, -⟩ := runsG_total h hc (k := n) fun ys hy ↦ ⟨ys, _, hy ▸ runsTo_readN s ys⟩
  have hr := runsTo_readN s xs
  rw [hl] at hr
  obtain ⟨rfl, rfl, rfl⟩ := runsG_on h hr hc
  exact ⟨rfl, hl, rfl, rfl⟩

theorem runsG_require_inv' {c : Prop} [Decidable c] {s t : Fs} {g : Option E} {xs : List E}
    {u : Unit} (h : RunsG (VerifierProgram.require c) s none xs u t g) (hc : ∃ sp, s.Carries sp) :
    c ∧ xs = [] ∧ t = s ∧ g = none := by
  have hr := RunsG.require_inv h hc
  obtain ⟨-, et, eg, ex⟩ := RunsG.det h (RunsTo.toG (tb_runsTo_require hr s)) hc (r1 := [])
    (r2 := xs) (by simp)
  exact ⟨hr, by simpa using ex.symm, et, eg⟩

theorem runsG_sample_inv {s t : Fs} {g : Option E} {xs : List E} {a : E}
    (h : RunsG VerifierProgram.sampleChallenge s none xs a t g) (hc : ∃ sp, s.Carries sp) :
    xs = [] ∧ a = s.squeeze.1 ∧ t = s.squeeze.2 ∧ g = none := by
  obtain ⟨ea, et, eg, ex⟩ := RunsG.det h (RunsTo.toG (runsTo_sampleE s)) hc (r1 := [])
    (r2 := xs) (by simp)
  exact ⟨by simpa using ex.symm, ea, et, eg⟩

theorem runsG_carries {α : Type} {p : VerifierProgram α} {s t : Fs} {xs : List E} {a : α}
    (h : RunsG p s none xs a t none) (hc : ∃ sp, s.Carries sp) : ∃ sp, t.Carries sp :=
  RunsG.carries h hc

/-! ## The table loop on every `153` words -/

/-- A list cut in pieces of the given lengths. -/
def chunks : List ℕ → List E → List (List E)
  | [], _ => []
  | k :: ks, l => l.take k :: chunks ks (l.drop k)

theorem chunks_length : ∀ (ks : List ℕ) (l : List E), (chunks ks l).length = ks.length
  | [], _ => rfl
  | _ :: ks, l => by simp [chunks, chunks_length ks]

theorem chunks_flatten : ∀ (ks : List ℕ) (l : List E), l.length = ks.sum →
    (chunks ks l).flatten = l
  | [], l, h => by simp at h; simp [chunks, h]
  | k :: ks, l, h => by
    simp only [List.sum_cons] at h
    rw [chunks, List.flatten_cons, chunks_flatten ks (l.drop k) (by simp; omega),
      List.take_append_drop]

theorem chunks_getElem_length : ∀ (ks : List ℕ) (l : List E), l.length = ks.sum →
    ∀ i (hi : i < (chunks ks l).length), ((chunks ks l)[i]).length = ks.getD i 0
  | [], _, _, i, hi => absurd hi (by simp [chunks])
  | k :: ks, l, h, 0, _ => by simp only [List.sum_cons] at h; simp [chunks]; omega
  | k :: ks, l, h, i + 1, hi => by
    simp only [List.sum_cons] at h
    simp only [chunks, List.getElem_cons_succ, List.getD_cons_succ]
    exact chunks_getElem_length ks (l.drop k) (by simp; omega) i (by simpa [chunks] using hi)

/-- The tables' widths, table by table. -/
theorem vt_tables_widths : ∀ t < 6, (tables.getD t default).width = vtW6.getD t 0 := by decide

/-- **Rows of the tables, with their evaluations cut from `153` words.** -/
theorem zip_chunks {X : Type} (rows : List (Table × X)) (hrows : rows.map (·.1) = tables)
    (ys : List E) (hy : ys.length = 153) :
    (List.zip rows (chunks vtW6 ys)).map (·.1) = rows ∧
      (List.zip rows (chunks vtW6 ys)).flatMap (·.2) = ys ∧
      ∀ p ∈ List.zip rows (chunks vtW6 ys), p.2.length = p.1.1.width := by
  have hrl : rows.length = 6 := by
    have : rows.length = tables.length := by simpa using congrArg List.length hrows
    rw [this]; rfl
  have hcl : (chunks vtW6 ys).length = 6 := by rw [chunks_length]; rfl
  refine ⟨List.map_fst_zip (by omega), ?_, fun p hp ↦ ?_⟩
  · rw [vt_flatMap_snd, List.map_snd_zip (by omega), chunks_flatten _ _ (by rw [hy]; rfl)]
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    simp only [List.length_zip] at hi
    simp only [List.getElem_zip]
    rw [chunks_getElem_length _ _ (by rw [hy]; rfl)]
    have h1 : rows[i].1 = tables[i]'(by simp [← hrows]; omega) := by
      have := congrArg (·[i]?) hrows
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (by rw [← hrows]; simp; omega)] at this
      simpa using this
    rw [h1, ← List.getD_eq_getElem _ default, vt_tables_widths i (by omega)]

/-- **The table loop runs on every `153` words.** -/
theorem tableTerms_any (cp fp point : List E) (hs : List ℕ) (fs : List (List Form)) (ws : List E)
    (h1 : 6 ≤ hs.length) (h2 : 6 ≤ fs.length) (h3 : 6 ≤ ws.length) (u : Fs) (ys : List E)
    (hy : ys.length = 153) :
    ∃ (b : E × List ColumnClaim) (v : Fs),
      RunsTo (tableTermsClaims cp fp point (List.zip tables (List.zip hs (List.zip fs ws))) 0 0 [])
        u ys b v := by
  obtain ⟨e1, e2, hw⟩ := zip_chunks (List.zip tables (List.zip hs (List.zip fs ws)))
    (List.map_fst_zip (by simp only [List.length_zip]; show 6 ≤ _; omega)) ys hy
  have h := vt_runsTo_tableTerms cp fp point _ 0 0 [] u hw
  rw [e1, e2] at h
  exact ⟨_, _, h⟩

/-! ## `tablesSeg` -/

theorem list_two {l : List E} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem list_eight {l : List E} (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩

theorem bytecodeAt_claimed' (bytecode : List K) (cl : BytecodeClaim) (pt : List E) (v : E)
    (h : pt = cl.bytecodePoint ∧ v = cl.bytecodeValue) :
    BytecodeAt (claimedBytecodeValue cl) bytecode pt v := by
  intro s
  simp [claimedBytecodeValue, tbRun, VerifierProgram.require, h, Compile.runWithHash]
  rfl

/-- **An accepting run of `tablesSeg` on a claimed evaluator, read back.** -/
theorem vt_inv {cl : BytecodeClaim} {bc : List K} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    {pi : Digest} {weights point values : List E} {beta : E} {f xs : List E}
    {res : BusResult × List ColumnClaim} {s' : Fs}
    (h : RunsTo (tablesSeg (claimedBytecodeValue cl) (layoutOf bc lm rows) pi weights beta point
      values) ⟨f, []⟩ xs res s')
    (hc : ∃ sp, (⟨f, []⟩ : Fs).Carries sp) :
    ∃ x4 bcW xR evs : List E, xs = x4 ++ bcW ++ xR ++ evs ∧ x4.length = 4 ∧ bcW.length = 10 ∧
      xR.length = 3 * (tableHeightsOf rows).foldl max 0 ∧ evs.length = 153 ∧ s'.pend = [] ∧
      BytecodeAt (claimedBytecodeValue cl) (layoutOf bc lm rows).bytecode
        (point.take (layoutOf bc lm rows).logBytecode ++
          bcSlots ((⟨f, []⟩ : Fs).absorbAll x4 dsObserve) bcW) (bcW.getD 9 0) := by
  generalize hL : layoutOf bc lm rows = L at h ⊢
  have hhL : L.tableLogHeights = tableHeightsOf rows := by rw [← hL]; rfl
  set s0 : Fs := ⟨f, []⟩ with hs0
  unfold tablesSeg at h
  obtain ⟨a1, xA, xB, t1, g1, hxs, rA, kA⟩ := RunsG.unbind (RunsTo.toG h) hc
  have rA0 := rA
  unfold busRest at rA
  dsimp only at rA
  -- the framework words
  obtain ⟨m, xm, xA1, u1, gu1, hA1, r1, k1⟩ := RunsG.unbind rA hc
  obtain ⟨rfl, lm2, rfl, rfl⟩ := runsG_readN_inv r1 hc
  have c1 := runsG_carries r1 hc
  obtain ⟨mf, xmf, xA2, u2, gu2, hA2, r2, k2⟩ := RunsG.unbind k1 c1
  obtain ⟨rfl, rfl, rfl⟩ := runsG_readE_inv r2 c1
  have c2 := runsG_carries r2 c1
  obtain ⟨bf, xbf, xA3, u3, gu3, hA3, r3, k3⟩ := RunsG.unbind k2 c2
  obtain ⟨rfl, rfl, rfl⟩ := runsG_readE_inv r3 c2
  have c3 := runsG_carries r3 c2
  -- the bytecode share
  obtain ⟨⟨sh, bp, val⟩, xS, xA4, u4, gu4, hA4, r4, k4⟩ := RunsG.unbind k3 c3
  have r40 := r4
  unfold bytecodeShare at r4
  obtain ⟨sh', xs1, xS1, v1, gv1, hS1, q1, q1k⟩ := RunsG.unbind r4 c3
  obtain ⟨rfl, rfl, rfl⟩ := runsG_readE_inv q1 c3
  have d1 := runsG_carries q1 c3
  obtain ⟨⟨chs, claim⟩, xs2, xS2, v2, gv2, hS2, q2, q2k⟩ := RunsG.unbind q1k d1
  obtain ⟨l8, -⟩ := runsG_total q2 d1 (k := 8) fun ys hy ↦
    ⟨_, _, bc_run _ _ (n := busBits) (by rw [hy]; rfl)⟩
  obtain ⟨e2, rfl, rfl⟩ := runsG_on q2 (bc_run _ _ (n := busBits) (by rw [l8]; rfl)) d1
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  have d2 := runsG_carries q2 d1
  dsimp only at q2k
  obtain ⟨val', xs3, xS3, v3, gv3, hS3, q3, q3k⟩ := RunsG.unbind q2k d2
  obtain ⟨rfl, rfl, rfl⟩ := runsG_readE_inv q3 d2
  have d3 := runsG_carries q3 d2
  obtain ⟨u, xs4, xS4, v4, gv4, hS4, q4, q4k⟩ := RunsG.unbind q3k d3
  obtain ⟨hreq, rfl, rfl, rfl⟩ := runsG_require_inv' q4 d3
  obtain ⟨eret, rfl, rfl, rfl⟩ := RunsG.ret_inv q4k d3
  simp only [Prod.mk.injEq] at eret
  obtain ⟨rfl, rfl, rfl⟩ := eret
  -- the claimed evaluator
  dsimp only at k4
  obtain ⟨u5, xe, xA5, u6, gu6, hA5, r5, k5⟩ := RunsG.unbind k4 (runsG_carries r4 c3)
  unfold claimedBytecodeValue at r5
  obtain ⟨hcl, rfl, rfl, rfl⟩ := runsG_require_inv' r5 (runsG_carries r4 c3)
  -- the bus, as a whole
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, rfl⟩ := list_eight l8
  set bcW : List E := [sh, y0, y1, y2, y3, y4, y5, y6, y7, val] with hbcW
  set u3' := ((s0.absorbAll xm dsObserve).absorb mf dsObserve).absorb bf dsObserve with hu3
  have hsl : bcSlots u3' bcW = (List.range busBits).map (bcCh (u3'.absorb sh dsObserve) sh
      [y0, y1, y2, y3, y4, y5, y6, y7]) := rfl
  have hreq' : bcClaim u3' bcW = dot (eqKernel (bcSlots u3' bcW)) weights * bcW.getD 9 0 := hreq
  have hbv : BytecodeAt (claimedBytecodeValue cl) L.bytecode
      (point.take L.logBytecode ++ bcSlots u3' bcW) val :=
    bytecodeAt_claimed' _ _ _ _ ⟨by rw [hsl]; exact hcl.1, hcl.2⟩
  have hsh := bcShare_run weights (point.take L.logBytecode) u3' (bcW := bcW) rfl hreq'
  obtain ⟨m0, m1, hm⟩ := list_two lm2
  have hs3 : u3' = s0.absorbAll (xm ++ [mf, bf]) dsObserve := by
    rw [hu3, hm]; rfl
  have hfw := vt_busRest_run (claimedBytecodeValue cl) L weights beta point values xm lm2 mf bf
    sh val (bcSlots u3' bcW) bcW s0 _ (hsh.of_eq hs3 rfl rfl rfl) hbv
  obtain ⟨ea1, et1, eg1, ex5⟩ := RunsG.det rA0 (RunsTo.toG hfw) hc (r1 := xB) (r2 := xA5 ++ xB)
    (by rw [hA1, hA2, hA3, hA4, hS1, hS2, hS3, hS4, hA5, hbcW]; simp)
  have hx5 : xA5 = [] := by simpa using ex5
  subst ea1 et1 eg1 hx5
  have cB := runsG_carries rA0 hc
  -- the table phase
  obtain ⟨a2, xC, xD, t2, g2, hxB, rT, kT⟩ := RunsG.unbind kA cB
  unfold tablePhaseClaims at rT
  dsimp only at rT
  obtain ⟨u0, ys0, ys1, w0, h0, hy0, p0, p0k⟩ := RunsG.unbind rT cB
  obtain ⟨-, rfl, rfl, ey0⟩ := RunsG.det p0 (RunsTo.toG (runsTo_grind0
    (bits := grindingBits ((tables.map Table.nConstraints).sum + nTrees - 1)) (by decide) _))
    cB (r1 := ys1) (r2 := ys0 ++ ys1) (by simp)
  have ey0' : ys0 = [] := by simpa using ey0
  subst ey0'
  obtain ⟨xi, ys2, ys3, w1, h1, hy1, p1, p1k⟩ := RunsG.unbind p0k cB
  obtain ⟨rfl, rfl, rfl, rfl⟩ := runsG_sample_inv p1 cB
  have cS := runsG_carries p1 cB
  obtain ⟨tc, zs1, zs2, w2, h2, hz, p2, p2k⟩ := RunsG.unbind p1k cS
  obtain ⟨-, rfl, rfl, rfl⟩ := RunsG.ret_inv p2k (RunsG.carries p2 cS)
  unfold tableSumcheckClaims at p2
  dsimp only at p2
  obtain ⟨⟨ch, cl'⟩, v1s, v2s, w3, h3, hv, m1, m2⟩ := RunsG.unbind p2 cS
  rw [hhL] at m1
  obtain ⟨l3, -⟩ := runsG_total m1 cS (k := 3 * (tableHeightsOf rows).foldl max 0) fun ys hy ↦
    ⟨_, _, zc_run _ _ hy⟩
  obtain ⟨-, rfl, rfl⟩ := runsG_on m1 (zc_run _ _ l3) cS
  have cZ := runsG_carries m1 cS
  dsimp only at m2
  obtain ⟨⟨fin, cls⟩, x1, x2, w4, h4, hx, n1, n2⟩ := RunsG.unbind m2 cZ
  have hf : (vtBus L weights beta point values xm mf bf sh (bcSlots u3' bcW)).forms.length = 6 := by
    rw [← hL]
    exact (vt_forms3_shape bc lm hr weights beta point xm mf bf sh (values.getD 0 0)
      (values.getD 1 0) (values.getD 2 0)).1
  have h6 : L.tableLogHeights.length = 6 := by rw [hhL]; exact vt_tableHeights_length hr
  obtain ⟨l153, -⟩ := runsG_total n1 cZ (k := 153) fun ys hy ↦ tableTerms_any _ _ _ _ _ _
    (by rw [h6]) (by rw [hf]) (by rw [LeanVM.Protocol.EndToEnd.Complete.length_tableWeights, h6])
    _ ys hy
  obtain ⟨-, -, eg4⟩ := runsG_on n1 (tableTerms_any _ _ _ _ _ _
    (by rw [h6]) (by rw [hf]) (by rw [LeanVM.Protocol.EndToEnd.Complete.length_tableWeights, h6])
    _ x1 l153).choose_spec.choose_spec cZ
  subst eg4
  have cT := runsG_carries n1 cZ
  obtain ⟨u7, y1s, y2s, w5, h5, hy', o1, o2⟩ := RunsG.unbind n2 cT
  obtain ⟨-, rfl, rfl, rfl⟩ := runsG_require_inv' o1 cT
  obtain ⟨-, rfl, rfl, rfl⟩ := RunsG.ret_inv o2 cT
  -- the public input
  obtain ⟨pc, p1s, p2s, w6, h6', hp, o3, o4⟩ := RunsG.unbind kT (RunsG.carries rT cB)
  obtain ⟨-, rfl, rfl, ep⟩ := RunsG.det o3 (RunsTo.toG (vt_publicInputPhase_run L pi _))
    (RunsG.carries rT cB) (r1 := p2s) (r2 := p1s ++ p2s) (by simp)
  have ep' : p1s = [] := by simpa using ep
  subst ep'
  obtain ⟨-, rfl, -, rfl⟩ := RunsG.ret_inv o4
    (RunsTo.carries (vt_publicInputPhase_run L pi _) (RunsG.carries rT cB))
  refine ⟨xm ++ [mf, bf], bcW, v1s, x1, ?_, by simp [lm2], rfl, l3, l153, rfl, ?_⟩
  · rw [hxs, hA1, hA2, hA3, hA4, hS1, hS2, hS3, hS4, hA5, hxB, hy0, hy1, hz, hv, hx, hy', hp, hbcW]
    simp
  · rw [← hs3]
    exact hbv

end
end LeanVM.Guest.B1.Tables
