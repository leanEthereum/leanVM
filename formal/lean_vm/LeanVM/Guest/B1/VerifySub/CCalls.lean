/-
  LeanVM.Guest.B1.VerifySub.CCalls

  `verify_sub`'s three phase calls, complete: GKR, the tables and Flock, from the callees'
  completeness over their honest scratch.
-/

module

public import LeanVM.Guest.B1.VerifySub.CBus

/-!
# GKR, the tables and Flock, complete (G:2150-2168)

The stream at the cursors (`stream_at`), each callee's soundness outcome at the honest run
(`gkrOut_honest`, `tablesOut_honest`, `flockOut_honest`), and the block (`c_calls`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs}

/-! ## The stream -/

theorem readsAt_left {p : E} {a b : List E} (h : ReadsAt rd p (a ++ b)) : ReadsAt rd p a :=
  fun k hk => by
    have := h k (by simp; omega)
    rwa [List.getElem_append_left hk] at this

theorem readsAt_right {p : E} {a b : List E} (h : ReadsAt rd p (a ++ b)) :
    ReadsAt rd (p * gen ^ a.length) b := fun k hk => by
  have := h (a.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rw [loadHolds_mul_gen_pow]; exact this

/-- **The phases' words at their cursors.** -/
theorem stream_at (hl : D.rows.length = 6) (h : ReadsAt rd P.stream D.stream) :
    ReadsAt rd (curG P) D.xsG ∧ ReadsAt rd (curT D P) D.xsT ∧ ReadsAt rd (curF D P) D.xsF ∧
      ReadsAt rd (curW D P) D.xsW := by
  have h1 : ReadsAt rd (P.stream * gen ^ 10) D.tail := by
    have := readsAt_right (a := D.ann ++ [D.x0, D.x1]) (b := D.tail) (by
      simpa [VsData.stream, List.append_assoc] using h)
    rwa [List.length_append, ann_length hl] at this
  refine ⟨readsAt_left h1, ?_, ?_, ?_⟩
  · exact readsAt_left (readsAt_right h1)
  · exact readsAt_left (readsAt_right (readsAt_right h1))
  · exact readsAt_right (readsAt_right (readsAt_right h1))

/-! ## The callees' outcomes at the honest run -/

variable {bytecode : List K} {out : E}

theorem depth_eq (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) :
    D.gr.2.1.length = log2Ceil D.pushTotal := by
  rw [hok.point_length, pushDepth_eq hb _ _ hok.rows_length]; rfl

theorem values_eq (hok : D.Ok bytecode) :
    D.gr.2.2 = [D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0] := by
  have := hok.values_length
  match h : D.gr.2.2, this with
  | [a, b, c], _ => rfl

theorem gkrOut_honest (hok : D.Ok bytecode) (hz : ReadsAt rd P.zeta D.gr.2.1)
    (hxs : ReadsAt rd (curG P) D.xsG) :
    GkrOut rd (digestScalars D.cvB).1 (digestScalars D.cvB).2 (curG P) (gen ^ D.gr.2.1.length) P.zeta
      ([(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P] ++ D.gr.2.2) :=
  ⟨D.cvB, D.gr.2.1.length, D.xsG, D.gr, D.cvG, rfl, rfl, by rw [hok.point_length]; exact hok.depth_lt,
    hxs, by rw [hok.point_length]; exact hok.gkr, rfl, hok.values_length, hz, rfl⟩

/-- `verify_tables`' arguments at the honest run. -/
def tabArgs (D : VsData) (P : VsPtrs) (sq : E) : List E :=
  [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, (digestScalars D.pi).1,
    (digestScalars D.pi).2, P.zeta, gen ^ D.gr.2.1.length, P.dims, P.rows, P.bk, sq, P.fpw, D.beta,
    P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]

/-- `verify_tables`' return words at the honest run. -/
def tabRets (D : VsData) (P : VsPtrs) : List E :=
  [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm]

theorem hs_length (hok : D.Ok bytecode) : D.hs.length = 6 := by
  simp [VsData.hs, hok.rows_length]

theorem dims_eq : gen ^ D.logMem :: D.hs.map (gen ^ ·) =
    gen ^ D.logMem :: D.rows.map fun n ↦ gen ^ log2Ceil n := by
  simp [VsData.hs, List.map_map, Function.comp_def]

theorem tablesPre_honest {lp sq : E} (hok : D.Ok bytecode) (ht : ExpTables rd lp sq)
    (hm : VsMem0 rd D P out) :
    TablesPre rd lp D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 (tabArgs D P sq) :=
  ⟨rfl, hm.zeta, rfl, by rw [hok.point_length]; exact hok.depth_lt, hok.logMem_ge, hok.logMem_le,
    ⟨D.hs.map (gen ^ ·), by simp [hs_length hok], hm.dims, hm.bk⟩, ht, by simp [VsData.alphas, sqAll_eq],
    hm.fpw, values_eq hok⟩

theorem tablesOut_honestQ {sq : E} {Q : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) (hxs : ReadsAt rd (curT D P) D.xsT)
    (hQ : Q rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims
      [P.zeta, P.chi, D.rm, gen ^ D.gr.2.1.length, D.gzcn, P.cplen]) :
    TablesOut bytecode Q rd D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 (tabArgs D P sq)
      (tabRets D P) :=
  ⟨D.cvG, D.xsT, D.cvT, D.rows, D.bus, D.claims, rfl, hok.rows_length, hm.rows,
    by rw [← dims_eq]; exact hm.dims, hok.rows_log, hxs, hok.tables, hok.claims_length, hm.pool,
    hQ, rfl, rfl⟩

theorem tablesOut_honest {sq : E} (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hxs : ReadsAt rd (curT D P) D.xsT) :
    TablesOut bytecode NoCtx rd D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 (tabArgs D P sq)
      (tabRets D P) :=
  tablesOut_honestQ hok hm hxs trivial

theorem tau_lt (hok : D.Ok bytecode) : D.tau < 29 := by
  unfold VsData.tau VsData.hs
  rw [List.getD_eq_getElem _ _ (by simp [hok.rows_length]), List.getElem_map]
  exact hok.rows_log _ (List.getElem_mem _)

theorem flockOut_honest (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hxs : ReadsAt rd (curF D P) D.xsF) :
    FlockOut rd D.tau (digestScalars D.cvT).1 (digestScalars D.cvT).2 (curF D P) P.zchis P.lrs
      P.zpart [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv] :=
  ⟨D.cvT, D.xsF, D.cvF, D.zSkip, D.alpha, D.mv, D.chi, D.rcs, D.s, rfl, hxs, hok.chi_length,
    hok.rcs_length, hok.s_length, hm.zchis, hm.lrs, hm.zpart, hok.flock, rfl⟩

/-! ## The block -/

/-- The values the three calls leave. -/
def callsOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(709, P.chi), (713, D.gzcn), (714, D.bv), (715, D.rm), (718, gen ^ D.tau),
    (720, gen ^ D.tau * word 256 0 0), (721, P.zchis),
    (722, P.lrs), (723, P.zpart), (726, curW D P), (727, D.zSkip), (728, D.alpha), (729, D.mv),
    (730, (digestScalars D.cvF).1), (731, (digestScalars D.cvF).2), (732, P.mcs), (733, P.ctab),
    (734, P.zvals)]

/-- The values the calls read. -/
def callsIn (D : VsData) (P : VsPtrs) (sq : E) : List (ℕ × E) :=
  [(0, (digestScalars D.pi).1), (1, (digestScalars D.pi).2), (5, sq), (7, P.pool), (8, P.cplen),
    (30, P.rows), (143, P.dims), (163, P.bk), (417, gen ^ log2Ceil D.pushTotal), (418, P.zeta),
    (508, P.fpw), (690, (digestScalars D.cvB).1), (691, (digestScalars D.cvB).2), (698, D.beta),
    (700, curG P)]

theorem dims_six (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    LoadHolds rd P.dims 6 (gen ^ D.tau) := by
  have := hm.dims 6 (by simp [hs_length hok])
  simp only [List.getElem_cons_succ, List.getElem_map] at this
  convert this using 2
  unfold VsData.tau
  rw [List.getD_eq_getElem _ _ (by simp [hs_length hok])]

/-- GKR's relation at the honest run, from its completeness. -/
theorem gkr_rel {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} {lp sq : E} (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode rd D P lp sq)
    (hG : CompleteGkr rd GMem) :
    coreProgram.Rel rd "verify_bus_gkr" [(digestScalars D.cvB).1, (digestScalars D.cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta]
      [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0] := by
  obtain ⟨hxG, -, -, -⟩ := stream_at hok.rows_length hm.stream
  have := hG P.gkr _ _ _ _ _ _ (gkrOut_honest hok hm.zeta hxG) hcal.gkr
  rw [depth_eq hb hok, values_eq hok] at this
  exact this

/-- The tables' relation at the honest run, from their completeness. -/
theorem tables_rel {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} {lp sq : E} (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out)
    (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode rd D P lp sq)
    (hT : CompleteTables bytecode rd TMem) :
    coreProgram.Rel rd "verify_tables" [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, D.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0,
      D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]
      [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm] := by
  obtain ⟨-, hxT, -, -⟩ := stream_at hok.rows_length hm.stream
  have hTab : coreProgram.Rel rd "verify_tables" (tabArgs D P sq) (tabRets D P) :=
    hT P.tab lp D.pi D.logMem D.alphas D.gr.2.1 D.gr.2.2 _ _ (tablesPre_honest hok ht hm)
      (tablesOut_honest hok hm hxT) hcal.tab
  rw [tabArgs, tabRets, depth_eq hb hok] at hTab; exact hTab

/-- Flock's relation at the honest run, from its completeness. -/
theorem flock_rel {GMem TMem FMem PMem : Reader → List E → List E → List E → Prop}
    {OMem : ℕ → ℕ → Reader → List E → List E → List E → Prop}
    {EMem : Reader → List E → List E → Prop} {lp sq : E}
    (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hcal : VsCallees GMem TMem FMem PMem OMem EMem bytecode rd D P lp sq)
    (hF : CompleteFlock rd FMem) :
    coreProgram.Rel rd "verify_flock" [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P,
      gen ^ D.tau, P.zchis, P.lrs, P.zpart]
      [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv] := by
  obtain ⟨-, -, hxF, -⟩ := stream_at hok.rows_length hm.stream
  exact hF P.fl D.tau _ _ _ _ _ _ _ (tau_lt hok) (flockOut_honest hok hm hxF) hcal.fl

/-- **GKR, the tables and Flock** (G:2150-2168). -/
theorem c_calls {lp sq : E} (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk C bytecode D P lp sq) (σ : Val) (hσ : Fixes σ (callsIn D P sq)) :
    Completes C rd 701 735 bCalls σ (fun σ' => Fixes σ' (callsOut D P)) := by
  have e : ∀ k e, (k, e) ∈ callsIn D P sq → σ (.n k) = e := fun k e h => hσ.get h
  refine completes_upds [(701, (digestScalars D.cvG).1), (702, (digestScalars D.cvG).2),
    (703, curT D P), (704, D.gr.2.2.getD 0 0), (705, D.gr.2.2.getD 1 0), (706, D.gr.2.2.getD 2 0),
    (707, (digestScalars D.cvG).1), (708, (digestScalars D.cvG).2), (709, P.chi),
    (710, (digestScalars D.cvT).1), (711, (digestScalars D.cvT).2), (712, curF D P), (713, D.gzcn),
    (714, D.bv), (715, D.rm), (716, (digestScalars D.cvT).1), (717, (digestScalars D.cvT).2),
    (718, gen ^ D.tau), (719, word 256 0 0), (720, gen ^ D.tau * word 256 0 0), (721, P.zchis),
    (722, P.lrs), (723, P.zpart), (724, (digestScalars D.cvF).1), (725, (digestScalars D.cvF).2),
    (726, curW D P), (727, D.zSkip), (728, D.alpha), (729, D.mv), (730, (digestScalars D.cvF).1),
    (731, (digestScalars D.cvF).2), (732, P.mcs), (733, P.ctab), (734, P.zvals)] (by simp)
    (fun next kret hn => ?_) ?_
  · simp only [bCalls, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    simp only [e 0 (digestScalars D.pi).1 (by simp [callsIn]), e 1 (digestScalars D.pi).2 (by simp [callsIn]), e 5 sq (by simp [callsIn]),
      e 7 P.pool (by simp [callsIn]), e 8 P.cplen (by simp [callsIn]), e 30 P.rows (by simp [callsIn]),
      e 143 P.dims (by simp [callsIn]), e 163 P.bk (by simp [callsIn]), e 417 (gen ^ log2Ceil D.pushTotal) (by simp [callsIn]),
      e 418 P.zeta (by simp [callsIn]), e 508 P.fpw (by simp [callsIn]), e 690 (digestScalars D.cvB).1 (by simp [callsIn]),
      e 691 (digestScalars D.cvB).2 (by simp [callsIn]), e 698 D.beta (by simp [callsIn]), e 700 (curG P) (by simp [callsIn])]
    refine ⟨?_, trivial, trivial, trivial, ?_, trivial, trivial, dims_six hok hm, trivial, trivial,
      trivial, trivial, trivial, ?_, trivial, trivial, trivial, trivial, trivial, hn⟩
    · exact hC.gkr
    · exact hC.tables
    · exact hC.flock
  · intro p hp
    simp only [callsOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [upds_n]

end
end LeanVM.Guest.B1.VerifySub
