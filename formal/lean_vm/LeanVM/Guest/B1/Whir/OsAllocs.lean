/-
  LeanVM.Guest.B1.Whir.OsAllocs

  `open_stacked`'s `HeapBuf`s: where its body allocates them, their sizes, and the pointers its
  honest values give them.
-/

module

public import LeanVM.Guest.B1.Whir.OsBody
public import LeanVM.Guest.B1.Whir.OsPlace

/-!
# The buffers (TRIAGE #36)

`osAllocList cfg`: the body's `HeapBuf` hints, its pointer and size values: the head's eleven
fixed buffers, each level's squeeze run and row weights, the tail's challenges, the point, the
basis rows, the inner sums, each level's chain. `osAllocs_eq`: at the honest values they are
`osAllocVals cfg R`, of sizes `osSizes cfg`; `osAllocVals_ptrs`: with the run's pointers
`osPtrAt` they are the allocator's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The head's buffers' sizes. -/
def osHeadSizes (cfg : OsCfg) : List ℕ :=
  [4 * cfg.capLen, cfg.capLen, cfg.yrLen, 2 * cfg.levels.length, cfg.nFolds, cfg.levels.length,
    cfg.levels.length * cfg.maxQ, cfg.posLen, cfg.posLen, cfg.levels.length * 22, cfg.levels.length * 4]

/-- Every buffer's size, in allocation order. -/
def osSizes (cfg : OsCfg) : List ℕ :=
  osHeadSizes cfg ++ (List.range cfg.levels.length).flatMap (fun _ => [2 * (cfg.maxSq + 1), cfg.maxIl]) ++
    [5, 42, cfg.levels.length * 22, cfg.levels.length * 22, cfg.levels.length + 1] ++
    List.replicate cfg.levels.length (cfg.maxQ + 1)

/-- The head's buffers' pointers. -/
def osPtrList (P : OsPtrs) : List E :=
  [P.caps, P.flags, P.fmsg, P.roots, P.fch, P.betas, P.qw, P.qpos, P.qbp, P.oodz, P.ood]

/-- Every buffer's pointer and size, in allocation order. -/
def osAllocVals (cfg : OsCfg) (R : OsRun) : List (E × ℕ) :=
  (osPtrList R.P).zip (osHeadSizes cfg) ++
    (List.range cfg.levels.length).flatMap (fun l => [(R.sqz l, 2 * (cfg.maxSq + 1)), (R.rew l, cfg.maxIl)]) ++
    [(R.tchv, 5), (R.D.pt, 42), (R.D.ba, cfg.levels.length * 22), (R.D.bb, cfg.levels.length * 22),
      (R.D.ich, cfg.levels.length + 1)] ++
    (List.range cfg.levels.length).map (fun l => (R.D.chv l, cfg.maxQ + 1))

/-- The head's `HeapBuf` hints. -/
def osHeadAllocs : List (V × (ℕ ⊕ V)) := (List.range 11).map fun i => (.n (40 + 2 * i), .inr (.n (39 + 2 * i)))

/-- The levels' `HeapBuf` hints from level `lvl` at `s`, `n` of them. -/
def osLvsAllocs (cfg : OsCfg) : ℕ → OsSt → ℕ → List (V × (ℕ ⊕ V))
  | _, _, 0 => []
  | lvl, s, n + 1 =>
    [(.n ((osLvG cfg lvl s).2.k + 1), .inr (.n (osLvG cfg lvl s).2.k)),
      (.n ((osLvSq cfg lvl (osLvG cfg lvl s).2).2.k + (cfg.lv lvl).queries + 1),
        .inr (.n ((osLvSq cfg lvl (osLvG cfg lvl s).2).2.k + (cfg.lv lvl).queries)))] ++
      osLvsAllocs cfg (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) s).2 n

/-- The finish's `HeapBuf` hints from `st`, the tail's challenges at `tch`. -/
def osFinAllocs (cfg : OsCfg) (st : OsSt) (tch : ℕ) : List (V × (ℕ ⊕ V)) :=
  [(.n (st.k + 1), .inl 42), (.n (st.k + 1 + 44), .inr (.n (st.k + 1 + 43))),
    (.n (st.k + 1 + 46), .inr (.n (st.k + 1 + 45))), (.n (osFinBs cfg st tch + 1), .inr (.n (osFinBs cfg st tch)))] ++
    (List.range cfg.levels.length).map fun l =>
      (.n (osFinBs cfg st tch + 3 + 13 * l + 1), .inr (.n (osFinBs cfg st tch + 3 + 13 * l)))

/-- **The body's `HeapBuf` hints**, in order. -/
def osAllocList (cfg : OsCfg) : List (V × (ℕ ⊕ V)) :=
  osHeadAllocs ++ osLvsAllocs cfg 0 (osHead cfg).2 cfg.levels.length ++
    [(.n ((OsRun.sL cfg).k + 1), .inr (.n (OsRun.sL cfg).k))] ++ osFinAllocs cfg (OsRun.sT cfg) (OsRun.tch cfg)

/-- The pointer and size values of `HeapBuf` hints. -/
noncomputable def osAllocs (σ : Val) (l : List (V × (ℕ ⊕ V))) : List (E × ℕ) :=
  l.map fun x => (σ x.1, x.2.elim id fun s => logG (σ s))

theorem os_logG_gw {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (osGw e) = e := by
  rw [os_gw_eq (by omega), gen_pow_eq_ofK]; exact logG_spec he

theorem osLvsAllocs_eq {CA CB Csq : ℕ → CallRel} {cfg : OsCfg} {σ : Val} {sqz rew : ℕ → E}
    (h1 : 2 * (cfg.maxSq + 1) < 2 ^ 64 - 1) (h2 : cfg.maxIl < 2 ^ 64 - 1) :
    ∀ (n lvl : ℕ) (s : OsSt), OsLvsCallsOk CA CB Csq cfg σ sqz rew lvl s n →
      osAllocs σ (osLvsAllocs cfg lvl s n) =
        (List.range n).flatMap fun i => [(sqz (lvl + i), 2 * (cfg.maxSq + 1)), (rew (lvl + i), cfg.maxIl)]
  | 0, _, _, _ => rfl
  | n + 1, lvl, s, ⟨_, _, _, hsig, hn⟩ => by
    have ih := osLvsAllocs_eq h1 h2 n (lvl + 1) _ hn
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [osLvsAllocs, osAllocs, List.map_append] at ih ⊢
    rw [ih]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hsig.sqPtr, hsig.sqSize, hsig.rwPtr, hsig.rwSize,
      os_logG_gw h1, os_logG_gw h2, Nat.add_zero, List.cons_append, List.nil_append]
    congr 1; congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show lvl + 1 + i = lvl + i.succ by omega]

/-- The buffers' sizes fit an exponent. -/
structure OsSizesOk (cfg : OsCfg) : Prop where
  head : ∀ s ∈ osHeadSizes cfg, s < 2 ^ 64 - 1
  sq : 2 * (cfg.maxSq + 1) < 2 ^ 64 - 1
  il : cfg.maxIl < 2 ^ 64 - 1
  bas : cfg.levels.length * 22 < 2 ^ 64 - 1
  ich : cfg.levels.length + 1 < 2 ^ 64 - 1
  res : cfg.maxQ + 1 < 2 ^ 64 - 1

/-- **The body's buffers at the honest values.** -/
theorem osAllocs_eq {CA CB Csq : ℕ → CallRel} {cfg : OsCfg} {σ : Val} {R : OsRun} (hsz : OsSizesOk cfg)
    (hhead : ∀ i < 11, σ (.n (39 + 2 * i)) = osGw ((osHeadSizes cfg).getD i 0) ∧
      σ (.n (40 + 2 * i)) = (osPtrList R.P).getD i 0)
    (hlvs : OsLvsCallsOk CA CB Csq cfg σ R.sqz R.rew 0 (osHead cfg).2 cfg.levels.length)
    (hts : σ (.n (OsRun.sL cfg).k) = osGw 5 ∧ σ (.n ((OsRun.sL cfg).k + 1)) = R.tchv)
    (hfs : OsFinSig σ cfg (OsRun.sT cfg) (OsRun.tch cfg) R.D) :
    osAllocs σ (osAllocList cfg) = osAllocVals cfg R := by
  have hH : osAllocs σ osHeadAllocs = (osPtrList R.P).zip (osHeadSizes cfg) := by
    apply List.ext_getElem (by simp [osAllocs, osHeadAllocs, osPtrList, osHeadSizes])
    intro i h1 h2
    have hi : i < 11 := by simpa [osAllocs, osHeadAllocs] using h1
    obtain ⟨e1, e2⟩ := hhead i hi
    have hl : i < (osHeadSizes cfg).length := by simp [osHeadSizes]; omega
    have hl' : i < (osPtrList R.P).length := by simp [osPtrList]; omega
    simp only [osAllocs, osHeadAllocs, List.getElem_map, List.getElem_range, Sum.elim_inr, List.getElem_zip]
    rw [e1, e2, List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl',
      os_logG_gw (hsz.head _ (List.getElem_mem hl))]
  have hL := osLvsAllocs_eq hsz.sq hsz.il cfg.levels.length 0 (osHead cfg).2 hlvs
  simp only [Nat.zero_add] at hL
  have hF : osAllocs σ (osFinAllocs cfg (OsRun.sT cfg) (OsRun.tch cfg)) =
      [(R.D.pt, 42), (R.D.ba, cfg.levels.length * 22), (R.D.bb, cfg.levels.length * 22),
        (R.D.ich, cfg.levels.length + 1)] ++ (List.range cfg.levels.length).map (fun l => (R.D.chv l, cfg.maxQ + 1)) := by
    simp only [osAllocs, osFinAllocs, List.map_append, List.map_cons, List.map_nil, List.map_map, Sum.elim_inl,
      Sum.elim_inr, id, hfs.pt, hfs.ba, hfs.baSz, hfs.bb, hfs.bbSz, hfs.ich, hfs.ichSz, os_logG_gw hsz.bas,
      os_logG_gw hsz.ich]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, Sum.elim_inr, hfs.res l hl', hfs.resSz l hl', os_logG_gw hsz.res]
  simp only [osAllocList, osAllocVals, osAllocs, List.map_append] at hH hL hF ⊢
  rw [hH, hL, hF]
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, hts.1, hts.2, os_logG_gw (show 5 < 2 ^ 64 - 1 by norm_num),
    List.append_assoc, List.cons_append, List.nil_append]

/-! ## The allocator's pointers -/

/-- Buffer `j`'s pointer from `b`. -/
def osPtrAt (cfg : OsCfg) (b j : ℕ) : E := ofK (gpow ((bases b (osSizes cfg)).getD j 0))

/-- The head's pointers from `b`. -/
def osPtrsOf (cfg : OsCfg) (b : ℕ) : OsPtrs :=
  ⟨osPtrAt cfg b 0, osPtrAt cfg b 1, osPtrAt cfg b 2, osPtrAt cfg b 3, osPtrAt cfg b 4, osPtrAt cfg b 5,
    osPtrAt cfg b 6, osPtrAt cfg b 7, osPtrAt cfg b 8, osPtrAt cfg b 9, osPtrAt cfg b 10⟩

/-- The run's pointers are the allocator's from `b`. -/
structure OsPtrsFrom (cfg : OsCfg) (b : ℕ) (R : OsRun) : Prop where
  P : R.P = osPtrsOf cfg b
  sqz : ∀ l, R.sqz l = osPtrAt cfg b (11 + 2 * l)
  rew : ∀ l, R.rew l = osPtrAt cfg b (11 + 2 * l + 1)
  tch : R.tchv = osPtrAt cfg b (11 + 2 * cfg.levels.length)
  pt : R.D.pt = osPtrAt cfg b (11 + 2 * cfg.levels.length + 1)
  ba : R.D.ba = osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)
  bb : R.D.bb = osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)
  ich : R.D.ich = osPtrAt cfg b (11 + 2 * cfg.levels.length + 4)
  chv : ∀ l, R.D.chv l = osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l)

theorem os_length_osSizes (cfg : OsCfg) :
    (osSizes cfg).length = 11 + 2 * cfg.levels.length + 5 + cfg.levels.length := by
  simp [osSizes, osHeadSizes, List.length_flatMap]; ring

private theorem os_range_map_getD (l : List ℕ) (f : ℕ → E) :
    (List.range l.length).map (fun j => f (l.getD j 0)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

private theorem os_flatMap_pairs (g : ℕ → E) (a : ℕ) : ∀ n,
    (List.range n).flatMap (fun l => [g (a + 2 * l), g (a + 2 * l + 1)]) = (List.range (2 * n)).map (fun i => g (a + i))
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, os_flatMap_pairs g a n, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      List.range_succ, List.range_succ]
    simp [List.map_append, Nat.add_assoc]

/-- **The sizes at the honest values.** -/
theorem osAllocVals_snd (cfg : OsCfg) (R : OsRun) : (osAllocVals cfg R).map Prod.snd = osSizes cfg := by
  simp only [osAllocVals, osSizes, List.map_append, List.map_flatMap, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def]
  rw [List.map_snd_zip (by simp [osPtrList, osHeadSizes]), List.map_const', List.length_range]

/-- **The pointers at the run's are the allocator's.** -/
theorem osAllocVals_fst {cfg : OsCfg} {b : ℕ} {R : OsRun} (h : OsPtrsFrom cfg b R) :
    (osAllocVals cfg R).map Prod.fst = (bases b (osSizes cfg)).map fun b' => ofK (gpow b') := by
  set n := cfg.levels.length
  have hl : (bases b (osSizes cfg)).length = 11 + 2 * n + 5 + n := by
    rw [os_length_bases, os_length_osSizes]
  rw [← os_range_map_getD (bases b (osSizes cfg)) (fun b' => ofK (gpow b')), hl, List.range_add, List.range_add,
    List.range_add]
  simp only [List.map_append, List.map_map, Function.comp_def]
  have e1 : (List.range 11).map (fun j => ofK (gpow ((bases b (osSizes cfg)).getD j 0))) = osPtrList R.P := by
    rw [h.P]; simp [List.range_succ, osPtrList, osPtrsOf, osPtrAt]
  have e2 := os_flatMap_pairs (osPtrAt cfg b) 11 n
  simp only [osAllocVals, List.map_append, List.map_flatMap, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def]
  rw [List.map_fst_zip (by simp [osPtrList, osHeadSizes]), e1]
  congr 1
  · congr 1
    · congr 1
      rw [List.flatMap_congr (fun l _ => by rw [h.sqz l, h.rew l]), e2]
      rfl
    · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
        h.tch, h.pt, h.ba, h.bb, h.ich, osPtrAt, Nat.add_assoc, List.cons_append, Nat.add_zero, n]
  · refine List.map_congr_left fun l _ => ?_
    rw [h.chv l]; rfl

end
end LeanVM.Guest.B1
