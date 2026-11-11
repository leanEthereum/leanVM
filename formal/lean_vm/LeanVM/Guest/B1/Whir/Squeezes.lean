/-
  LeanVM.Guest.B1.Whir.Squeezes

  A level's query positions and batching challenge: the template's squeeze block, with its loop,
  squeezes the Spec's `sampleQueries` and `sampleE`.
-/

module

public import LeanVM.Guest.B1.Whir.SqLoop
public import LeanVM.Guest.B1.Whir.Positions
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# The squeezes of a level

After the proof of work the sponge has nothing waiting. `level_positions` stores its capacity in
the squeeze run's row `0`, runs the squeeze loop (`lv.squeezes` squeezes, each decoding
`192/depth` positions) and returns the last capacity (`level_positions_sound`); the level
squeezes the batching challenge `lam` from it (`osPositions_sound`). In the Spec that is `sampleQueries` (V:1682; `sampleQueriesAux_run`) and
`sampleE`.

`PadOk σ pad`: the sponge's zero run, once allocated, holds zeros.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The zero run, once allocated, holds zeros after its first cell. -/
def PadOk (σ : Val) : Option ℕ → Prop
  | none => True
  | some p => σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧ σ (.n (p + 4)) = 0

theorem osPad_ok {pad : Option ℕ} {k : ℕ} (hp : PadOk σ pad) {C : CallRel}
    (h : AllOk C rd σ (osPad pad k).1) : PadOk σ (some (osPad pad k).2.1) := by
  cases pad with
  | some p => exact hp
  | none =>
    simp only [osPad, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
    obtain ⟨-, h1, h2, h3, h4⟩ := h
    simp only [PadOk, osPad]
    rw [h1, h2, h3, h4, word_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem osPad_next (pad : Option ℕ) (k : ℕ) : k ≤ (osPad pad k).2.2 := by
  cases pad <;> simp [osPad]

/-- A squeeze with nothing waiting (`osSqueeze0`) on the capacity values `cap`, the zero run at
`p` holding zeros: its outputs are the cells of the sponge's permutation, its challenge the
sponge's. -/
theorem osSqueeze0_val {C : CallRel} {p : ℕ} {cap : List ℕ} (hcl : cap.length = 5) {j : ℕ}
    (hp : PadOk σ (some p)) (h : AllOk C rd σ (osSqueeze0 p cap j)) :
    (∀ c : Fin 13, σ (.n (j + c.val)) =
      cellsOfState (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm false c) ∧
    σ (.n (j + 19)) = challengeOf (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm := by
  match cap, hcl with
  | [a0, a1, a2, a3, a4], _ =>
  simp only [osSqueeze0, allOk_cons, allOk_challengeT] at h
  obtain ⟨hK, hch⟩ := h
  obtain ⟨-, -, -, hout⟩ := keccakA_perm (rd := rd) hK
  obtain ⟨z1, z2, z3, z4⟩ := hp
  have hS : permOf (List.map σ (List.map V.n ([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3,
      p + 4] ++ [a0, a1, a2, a3, a4]))) =
      (⟨[a0, a1, a2, a3, a4].map fun i ↦ σ (.n i), []⟩ : Fs).perm := by
    rw [perm_eq_cells _ (by simp)]
    simp [pendCells, z1, z2, z3, z4]
  rw [hS] at hout
  have e : ∀ c : Fin 13, σ (.n (j + c.val)) =
      cellsOfState (⟨[a0, a1, a2, a3, a4].map fun i ↦ σ (.n i), []⟩ : Fs).perm false c :=
    fun c ↦ by simpa [osRun] using outs_eq hout c (by simp [osRun])
  refine ⟨e, ?_⟩
  have := challengeT_value hch (e 0) (e 1)
  simpa using this

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 →
    (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => by rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]

/-- A sponge with nothing waiting is its capacity. -/
theorem fs_of_pend_nil {s : Fs} (h : s.pend = []) : s = ⟨s.cap, []⟩ := by
  cases s; simp_all

/-! ## `level_positions` -/

/-- **`level_positions(fs0..fs4, positions, win_ptrs, win_tabs)`** at `sq` squeezes, a level of
tree depth `d` and cap depth `cd`: from the capacity `fs0..fs4` with nothing waiting, squeeze `j`
(`j < sq`) decodes its positions and windows at `positions·g^(j·(192/d))` and
`win_ptrs·g^(j·(192/d))`; it returns the capacity after the `sq` squeezes. -/
def MeaningLevelPositions (d cd sq : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, qpos, qbp, tabs], rets =>
      (∀ jj < sq, MeaningDecodeQueryWindows d cd rd
        [((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN jj).2.squeeze.1,
          qpos * gen ^ (jj * (192 / d)), qbp * gen ^ (jj * (192 / d)), tabs] []) ∧
      rets = ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN sq).2.cap
  | _, _ => False

/-- `level_positions`' body before its `ret`. -/
def lpA (sq : ℕ) (loop : String) : List Stmt :=
  osHeap ((sq + 1) * 5) 8 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n i) (.n 9) i)) ++
    osLoopCall loop sq [9, 5, 6, 7] 10 ++
    [.atom (.const (.n 15) (gw (sq * 5))), .atom (.mul (.n 16) (.n 9) (.n 15))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (17 + i)) (.n 16) i)) ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (22 + i)) (.n (17 + i))))

theorem lpBody_split (sq : ℕ) (loop : String) :
    lpBody sq loop = lpA sq loop ++ [.ret ((List.range 5).map fun i ↦ .n (22 + i))] := by
  simp only [lpBody, lpA, List.append_assoc]

theorem lpA_flat (sq : ℕ) (loop : String) : (lpA sq loop).all Stmt.flat = true := by
  simp [lpA, osHeap, osLoopCall, Stmt.flat]

/-- **`level_positions` is sound** at its specialization's template and its loop's. -/
theorem level_positions_sound {name loop : String} {sq d cd : ℕ}
    (hfn : FnIs name (osParams 8) (lpBody sq loop))
    (hloop : FnIs loop (osParams 6) (lpLoopBody d cd loop))
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd)
        args rets → MeaningDecodeQueryWindows d cd rd args rets)
    (hn0 : 0 < sq) (hn : sq < ordG) (hn5 : sq * 5 < u128Bound) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) (hwt : WinTabs rd (args.getD 7 0)) :
    MeaningLevelPositions d cd sq rd args rets := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [rel_iff_sem hf] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [hb, lpBody_split, holdsList_flat_ret _ (lpA_flat sq loop)] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [hps] at hp
  subst hp
  subst hret
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at hwt ⊢
  simp only [lpA, osHeap, osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk,
    Atom.Holds, List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, Nat.add_zero, Nat.reduceAdd, and_assoc] at hok
  obtain ⟨-, -, s0, s1, s2, s3, s4, c10, c11, a12, c13, c14, -, hcall, c15, m16,
    l17, l18, l19, l20, l21, e22, e23, e24, e25, e26⟩ := hok
  have hgn : gw sq = gen ^ sq := gw_eq (by
    have : ordG < u128Bound := by unfold ordG u128Bound; norm_num
    omega)
  have hit := lpLoop_sound hloop hpw hdec hn0 hn (σ (.n 9)) (σ (.n 5)) (σ (.n 6)) (σ (.n 7)) hwt
    (by rw [a12, c10, c11, c13, c14, hgn, word_one] at hcall; exact hcall)
  set fs := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]
  obtain ⟨P, D⟩ := sqChain (sqz := σ (.n 9)) fs rfl (fun i hi ↦ by
      rcases i with _ | _ | _ | _ | _ | i
      · exact s0
      · exact s1
      · exact s2
      · exact s3
      · exact s4
      · omega) hit
  have hrow : σ (.n 16) = σ (.n 9) * gen ^ (5 * sq) := by
    rw [m16, c15, gw_eq hn5, Nat.mul_comm]
  have hlast : [σ (.n 17), σ (.n 18), σ (.n 19), σ (.n 20), σ (.n 21)] =
      ((⟨fs, []⟩ : Fs).squeezeN sq).2.cap := by
    refine five_eq (o := 5 * sq) rfl ?_ (fun i hi ↦ ?_) (P sq le_rfl)
    · exact squeezeN_cap_length _ _ rfl
    · rw [← loadHolds_mul_gen_pow, ← hrow]
      rcases i with _ | _ | _ | _ | _ | i
      · exact l17
      · exact l18
      · exact l19
      · exact l20
      · exact l21
      · omega
  refine ⟨fun jj hjj ↦ by simpa using D jj hjj, ?_⟩
  rw [← hlast, e22, e23, e24, e25, e26]

/-- **A level's query positions and batching challenge**: from the capacity it carries with
nothing waiting, the dispatch on the rate into `level_positions` decodes the positions and their
windows at the level's slots (reading the window table at `win_tabs`), and the next squeeze is the
batching challenge `lam` (at the returned `k - 1`), its capacity the sponge's. -/
theorem osPositions_sound {C : CallRel} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hok : AllOk C rd σ (osPositions c lvl lv st).1)
    (hLP : ∀ args rets, C (osPositionsName lv) args rets → WinTabs rd (args.getD 7 0) →
      MeaningLevelPositions lv.depth lv.capDepth lv.squeezes rd args rets)
    (hrate : LvRate σ c lvl lv) (hwt : WinTabs rd (σ (.n osWin))) (hpo : lv.posOff < u128Bound)
    (hfs : st.fs.length = 5) (hpad : PadOk σ st.pad) (hmats : MatsOk σ st.mats) :
    (∀ jj < lv.squeezes, MeaningDecodeQueryWindows lv.depth lv.capDepth rd
      [((⟨st.fsv σ, []⟩ : Fs).squeezeN jj).2.squeeze.1,
        σ (.n osQpos) * gen ^ (lv.posOff + jj * (192 / lv.depth)),
        σ (.n osQbp) * gen ^ (lv.posOff + jj * (192 / lv.depth)), σ (.n osWin)] []) ∧
    σ (.n ((osPositions c lvl lv st).2.k - 1)) =
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ∧
    (osPositions c lvl lv st).2.fsv σ =
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.2.cap ∧
    PadOk σ (osPositions c lvl lv st).2.pad ∧ (osPositions c lvl lv st).2.fs.length = 5 ∧
    MatsOk σ (osPositions c lvl lv st).2.mats := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  set k := st.k
  set P := c.plan
  set qp := osMatP P st.mats osQpos lv.posOff k
  set m1 := osMatsAfter P st.mats osQpos lv.posOff k
  set wp := osMatP P m1 osQbp lv.posOff qp.2.2
  set j := wp.2.2
  set p := (osPad st.pad (j + 10)).2.1
  set e := (osPad st.pad (j + 10)).2.2
  have hsk : (osPositions c lvl lv st).2.k = e + 20 := rfl
  have hsfs : (osPositions c lvl lv st).2.fs = [e + 8, e + 9, e + 10, e + 11, e + 12] := rfl
  have hspad : (osPositions c lvl lv st).2.pad = some p := rfl
  have hsm : (osPositions c lvl lv st).2.mats = osMatsAfter P m1 osQbp lv.posOff qp.2.2 := rfl
  have hstm : (osPositions c lvl lv st).1 = qp.1 ++ wp.1 ++
      [.dispatch (.n osRate) ((c.lvAt lvl).map osPositionsName)
        ((st.fs ++ [qp.2.1, wp.2.1, osWin]).map V.n) (osRun j 5)] ++
      ((List.range 5).map fun i ↦ .atom (.copy (.n (j + 5 + i)) (.n (j + i)))) ++
      (osPad st.pad (j + 10)).1 ++ osSqueeze0 p [j + 5, j + 6, j + 7, j + 8, j + 9] e := rfl
  rw [hstm] at hok
  rw [hsk, hsfs, hspad, hsm]
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨hqp, hwp⟩, hD⟩, hcp⟩, hPd⟩, hQ⟩ := hok
  have mk1 := osMatsAfter_ok hmats hpo hqp
  have eqp := osMatP_val hmats hpo hqp
  have ewp := osMatP_val mk1 hpo hwp
  rw [allOk_cons] at hD
  have hcall := dispatch_rate hrate osPositionsName hD.1
  simp only [hf, osRun, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.range_succ, List.range_zero, Nat.add_zero] at hcall
  have hm := hLP _ _ hcall (by simpa using hwt)
  obtain ⟨hdec, hrets⟩ := hm
  have hfsv : st.fsv σ = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [OsSt.fsv, hf]
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil,
    List.range_succ, List.range_zero, List.nil_append, List.cons_append, Nat.add_zero,
    Nat.add_assoc, Nat.reduceAdd] at hcp
  obtain ⟨e5, e6, e7, e8, e9⟩ := hcp
  have hpad' := osPad_ok hpad hPd
  have hsq := osSqueeze0_val (cap := [j + 5, j + 6, j + 7, j + 8, j + 9]) rfl hpad' hQ
  have hF : (⟨[σ (.n (j + 5)), σ (.n (j + 6)), σ (.n (j + 7)), σ (.n (j + 8)),
      σ (.n (j + 9))], []⟩ : Fs) = ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 := by
    rw [e5, e6, e7, e8, e9, ← hrets.symm.trans rfl, hfsv]
    rw [← fs_of_pend_nil (squeezeN_pend rfl _)]
  simp only [List.map_cons, List.map_nil, hF] at hsq
  obtain ⟨hcells, hlam⟩ := hsq
  refine ⟨fun jj hjj ↦ ?_, by rw [show e + 20 - 1 = e + 19 by omega, hlam]; rfl, ?_, hpad', rfl,
    osMatsAfter_ok mk1 hpo hwp⟩
  · have := hdec jj hjj
    rw [eqp, ewp, mul_assoc, mul_assoc, ← pow_add, ← hfsv] at this
    exact this
  · have h8 : σ (.n (e + 8)) = _ := hcells 8
    have h9 : σ (.n (e + 9)) = _ := hcells 9
    have h10 : σ (.n (e + 10)) = _ := hcells 10
    have h11 : σ (.n (e + 11)) = _ := hcells 11
    have h12 : σ (.n (e + 12)) = _ := hcells 12
    rw [OsSt.fsv, hsfs]
    simp only [List.map_cons, List.map_nil, Fs.squeeze, capOf, h8, h9, h10, h11, h12]

end
end LeanVM.Guest.B1.Whir
