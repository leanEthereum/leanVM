/-
  LeanVM.Guest.B1.Bits.QueryWindowsAt

  `decode_query_windows` complete in the placed form `open_stacked`'s squeeze loop takes: its
  frame's `wins` run holds the honest windows, the caller's words its positions and pointers.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsComplete
public import LeanVM.Guest.Memory.LiftPure

/-!
# `decode_query_windows`, placed (`crates/rec_aggregation/guests/lean_ethereum.py`)

**The form** (`QwDecodeAtD`, the windowed successor of `OsDecodeAtD`): at every frame pointer
`fp`, for arguments whose loads lie in the caller's words (`QwRegs`: `positions` and `win_ptrs`
below `128 / d`, the window table `tabs` below `128`; `RegPtrs [(1, 128 / d), (2, 128 / d),
(3, 128)]` unfolded), on every memory defined below `2^k` where the caller's words hold the
window table, the word's positions and the pointers `g^(fp + cert name (.n 5))·g^(j·qwN)` into
the `wins` run (`qwPtrAt`), a tree of `fs name` words holds (the word bound: the function is a
leaf with no `HeapBuf`), its data holding the run of the honest windows (`qwRunL`: `qwRunList`,
the positions' windows in order, at the certificate's cell of `.n 5`).

**The lift** (`qwDecodeAtD_of`): the honest valuation (`qw_holds`) on the memory; its atoms are of
the kinds `QwEnv.Ok` names, so the walk's loads read the caller's words, its `frameAddr`s are
the run's address and its tails' (`run·g^(r - 5)`, the run's cells consecutive in the frame,
`RunsConsec`, the certificates' fact as `Lift.RunsFit` is), and `relAtIn_of_walk` places it.
`qwDecodeAtD_holds`: every deployed specialization (`QueryWindowsAtAll.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The form -/

/-- The `wins` run of the honest run at `fp`: the positions' windows at the certificate's cell of
`.n 5`. -/
def qwRunL (cert : String → V → ℕ) (name : String) (fp d cd : ℕ) (w : E) : Layout :=
  [(fp + cert name (.n 5), qwRunList d cd w)]

/-- Position `j`'s window pointer at `fp`: the `wins` run's address, shifted to the position's first
window. -/
def qwPtrAt (cert : String → V → ℕ) (name : String) (fp d cd j : ℕ) : E :=
  ofK (Parameters.addressOfIndex (fp + cert name (.n 5))) * gen ^ (j * qwN d cd)

/-- The loads of `decode_query_windows(word, positions, win_ptrs, tabs)` lie in `R`: `positions`
and `win_ptrs` below `128 / d`, `tabs` below `128` (`RegPtrs [(1, 128 / d), (2, 128 / d), (3, 128)]
[w, pos, ptrs, tabs] R`, unfolded). -/
def QwRegs (d : ℕ) (args : List E) (R : ℕ → Prop) : Prop :=
  ∀ p ∈ [(1, 128 / d), (2, 128 / d), (3, 128)], ∀ t < p.2,
    ∃ i, (args.getD p.1 0).limb 0 * Parameters.addressOfIndex t = Parameters.addressOfIndex i ∧ R i

/-- **`decode_query_windows__L{d}_L{cd}`, placed, on disjoint layouts**: at every frame pointer
`fp`, on every memory where the caller's words `Lin` hold the window table, the positions at `pos`
and the pointers `qwPtrAt` at `ptrs`, a tree of `fs name` words holds, its data holding the run
`qwRunL`, its other words `Lown`, its loads in its data or `Lin`. -/
def QwDecodeAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d cd : ℕ) (name : String) :
    Prop :=
  ∀ (w pos ptrs tabs : E) (Lin : Layout) (fp : ℕ),
    QwRegs d [w, pos, ptrs, tabs] (RegionL Lin) →
    (∀ rd, LowDef k rd → MemL rd Lin → WinTabs rd tabs ∧ ∀ j < 128 / d,
      LoadHolds rd pos j (eOfNat (qwPosOf d w j)) ∧ LoadHolds rd ptrs j (qwPtrAt cert name fp d cd j)) →
    ∃ Lown : Layout, Within (qwRunL cert name fp d cd w ++ Lown) fp (fs name) ∧
      DisjL (qwRunL cert name fp d cd w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (qwRunL cert name fp d cd w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (qwRunL cert name fp d cd w)) fp
          (fs name) name [w, pos, ptrs, tabs] []

/-- **Every frame run's cells are consecutive**: value `k` of a `frameAddr` run of a function's
body sits `k` cells past the run's first. The certificates' fact (`B2C.FnStatic.run`), as
`Lift.RunsFit` is. -/
def RunsConsec (cert : String → V → ℕ) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ p r rs,
    Atom.frameAddr p (r :: rs) ∈ Lift.blockAtoms fn.body →
    ∀ (k : ℕ) (hk : k < (r :: rs).length), cert f (r :: rs)[k] = cert f r + k

/-! ## The walk -/

theorem qw_mem_blockAtoms {a : Atom} : ∀ {ss : List Stmt}, Stmt.atom a ∈ ss → a ∈ Lift.blockAtoms ss
  | [], h => by cases h
  | s :: ss, h => by
    rw [Lift.blockAtoms, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp [Lift.stmtAtoms])
    · exact Or.inr (qw_mem_blockAtoms h)

/-- The body's statements before its `ret`. -/
def qwPre (d cd : ℕ) : List Stmt :=
  [.atom (.frameAddr (.n 4) qwRun)] ++ (qwPositions d cd 0 (128 / d) 41 none).1 ++
    (qwRest d 0 (qwRestN d) (qwPositions d cd 0 (128 / d) 41 none).2.1
      (qwPositions d cd 0 (128 / d) 41 none).2.2).1 ++
    [.atom (.assertEq ((qwRest d 0 (qwRestN d) (qwPositions d cd 0 (128 / d) 41 none).2.1
      (qwPositions d cd 0 (128 / d) 41 none).2.2).2.2.getD (.n 0)) (.n 0))]

theorem qwBody_eq (d cd : ℕ) : qwBody d cd = qwPre d cd ++ [.ret []] := by
  simp [qwBody, qwPre]

theorem qwPre_atoms (d cd : ℕ) : AllAtoms (qwPre d cd) := by
  refine allAtoms_append (allAtoms_of_all (qwBody_atoms d cd)) ?_
  exact allAtoms_cons allAtoms_nil

theorem qwPre_straight (d cd : ℕ) : (qwPre d cd).all Stmt.straight = true :=
  List.all_eq_true.mpr fun s hs ↦ by
    obtain ⟨a, rfl⟩ := qwPre_atoms d cd s hs
    rfl

theorem qw_ev_mem {σ : Val} {d cd : ℕ} {e : Ev} (he : e ∈ (qwPre d cd).flatMap (slEvs σ)) :
    ∃ a, Stmt.atom a ∈ qwBody d cd ∧ e = .atom a := by
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  obtain ⟨a, rfl⟩ := qwPre_atoms d cd s hs
  simp only [slEvs, List.mem_singleton] at he
  exact ⟨a, by rw [qwBody_eq]; exact List.mem_append_left _ hs, he⟩

/-! ## The lift -/

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`decode_query_windows__L{d}_L{cd}` placed**, from its template, the certificates' frame runs
fitting their frames and their cells consecutive. -/
theorem qwDecodeAtD_of {name : String} {d cd : ℕ} (hfit : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (hs : QwShape d cd) (hq : QwIs name (qwBody d cd)) {k : ℕ}
    (hk : 7 ≤ k) : QwDecodeAtD fs cert k d cd name := by
  obtain ⟨fn, hfind, hps, hbody⟩ := hq
  intro w pos ptrs tabs Lin fp hreg hpre
  have hM : 128 / d * qwN d cd ≤ 36 := hs.2.2.1
  have hrunA : Atom.frameAddr (.n 4) qwRun ∈ Lift.blockAtoms fn.body := by
    rw [hbody]; exact qw_mem_blockAtoms (by simp [qwBody])
  have hc5 : cert name (.n 5) + 36 ≤ fs name := by
    have h := hfit name fn hfind (.n 4) (.n 5) ((List.range 35).map fun i ↦ V.n (5 + (i + 1)))
      (by rw [← qwRun_eq]; exact hrunA)
    simpa using h
  have hcell : ∀ x < 36, cert name (.n (5 + x)) = cert name (.n 5) + x := fun x hx ↦ by
    have hx' : x < (V.n 5 :: (List.range 35).map fun i ↦ V.n (5 + (i + 1))).length := by
      simpa using hx
    have h := hcons name fn hfind (.n 4) (.n 5) ((List.range 35).map fun i ↦ V.n (5 + (i + 1)))
      (by rw [← qwRun_eq]; exact hrunA) x hx'
    have e : (V.n 5 :: (List.range 35).map fun i ↦ V.n (5 + (i + 1)))[x] = V.n (5 + x) := by
      rcases x with _ | x
      · rfl
      · simp [Nat.add_comm]
    rw [e] at h
    exact h
  refine ⟨[], fun q hq ↦ ?_, ?_, fun rd hlow hL ↦ ?_⟩
  · simp only [qwRunL, List.append_nil, List.mem_singleton] at hq
    subst hq
    simp only [qwRunList, List.length_map, List.length_range]
    omega
  · simp [DisjL, qwRunL]
  rw [List.append_nil] at hL
  obtain ⟨hR, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hT, hrd⟩ := hpre rd hlow hLin
  set run : E := ofK (Parameters.addressOfIndex (fp + cert name (.n 5))) with hrun
  have hlow7 : ∀ i < 128, (rd (Parameters.addressOfIndex i)).isSome := fun i hi ↦
    hlow i (lt_of_lt_of_le hi (by
      calc 128 = 2 ^ 7 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk))
  have hrunF : FrameRun rd run (128 / d * qwN d cd) (qwRunW d cd w) := by
    refine ⟨ofK_isInK _, fun i hi v hv ↦ ?_⟩
    have h := (hR _ (List.mem_singleton_self _) i (by simpa [qwRunList] using hi)).2
    rw [hv, Option.some.injEq] at h
    rw [h]
    simp [qwRunList]
  obtain ⟨σ, hp, hAK, -⟩ := qw_holds hs hlow7 hT hrunF fun j hj ↦ hrd j hj
  -- the walk
  have hw : walk σ fn.body = .ret ((qwPre d cd).flatMap (slEvs σ)) [] := by
    rw [hbody, qwBody_eq]
    exact walk_straight σ [] (qwPre d cd) (qwPre_straight d cd)
  set es := (qwPre d cd).flatMap (slEvs σ)
  have hes : ∀ e ∈ es, e.Holds rd σ := fun e he ↦ by
    obtain ⟨a, ha, rfl⟩ := qw_ev_mem he
    exact (hAK a ha).1
  have hcalls : calls es = [] := List.filterMap_eq_nil_iff.mpr fun e he ↦ by
    obtain ⟨a, -, rfl⟩ := qw_ev_mem he
    rfl
  have hal : allocs σ es = [] := List.filterMap_eq_nil_iff.mpr fun e he ↦ by
    obtain ⟨a, ha, rfl⟩ := qw_ev_mem he
    have hok := (hAK a ha).2
    cases a with
    | hint h => cases h <;> first | rfl | exact hok.elim
    | _ => rfl
  have hald : allocDsts es = [] := List.filterMap_eq_nil_iff.mpr fun e he ↦ by
    obtain ⟨a, ha, rfl⟩ := qw_ev_mem he
    have hok := (hAK a ha).2
    cases a with
    | hint h => cases h <;> first | rfl | exact hok.elim
    | _ => rfl
  have hp' := hp
  rw [← hps] at hp'
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, h1, h2, h3, -⟩ := hp
  have hrunEs : (V.n 5, 36) ∈ runs es := by
    refine List.mem_filterMap.mpr ⟨.atom (.frameAddr (.n 4) qwRun), ?_, by rw [qwRun_eq]; rfl⟩
    exact List.mem_flatMap.mpr ⟨.atom (.frameAddr (.n 4) qwRun), by simp [qwPre], by simp [slEvs]⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL (qwRunL cert name fp d cd w)) (Dk := fun _ => False) (N := 0) (fp := fp)
    coreProgram_wf hfind (Or.inr hcalls) hp' hw rfl hes (by rw [hald, hal]; rfl)
    (fun q hq ↦ ?_) (by rw [hcalls]; exact ⟨rfl, fun _ h => h⟩) (fun A hA ↦ ?_) (fun i hi ↦ ?_)
  · simpa only [hal, List.sum_nil, Nat.add_zero, List.map_nil] using h
  · -- a `frameAddr`: the run's address, or its tail's
    obtain ⟨e, he, hq⟩ := List.mem_filterMap.mp hq
    obtain ⟨a, ha, rfl⟩ := qw_ev_mem he
    have hok := (hAK a ha).2
    cases a with
    | frameAddr p run' =>
      cases run' with
      | nil => exact hok.elim
      | cons r rs =>
        simp only [Ev.addr?, Option.some.injEq] at hq
        subst hq
        obtain ⟨hr, hr5, hr61, hσ⟩ := hok
        obtain ⟨y, hy⟩ : ∃ y, r.idx = 5 + y := ⟨r.idx - 5, by omega⟩
        rw [hy] at hr hσ hr61
        rw [hr]
        show σ p = ofK (Parameters.addressOfIndex (fp + cert name (.n (5 + y))))
        rw [hσ, show 5 + y - 5 = y by omega, hcell y (by omega), gen_pow_eq_ofK, ← ofK_mul,
          Parameters.addressOfIndex, Parameters.addressOfIndex, Parameters.addressOfIndex, ← pow_add,
          Nat.add_assoc]
    | _ => simp [Ev.addr?] at hq
  · -- a load: the caller's words
    obtain ⟨e, he, hA⟩ := List.mem_filterMap.mp hA
    obtain ⟨a, ha, rfl⟩ := qw_ev_mem he
    have hok := (hAK a ha).2
    cases a with
    | load dv q off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hA
      subst hA
      rcases hok with ⟨hq, hoff⟩ | ⟨hq, hoff⟩ | ⟨e, he128, hq, rfl⟩
      · obtain ⟨i, hi, hRi⟩ := hreg (1, 128 / d) (by simp) off hoff
        exact ⟨i, by rw [hq]; exact hi, Or.inr (Or.inl hRi)⟩
      · obtain ⟨i, hi, hRi⟩ := hreg (2, 128 / d) (by simp) off hoff
        exact ⟨i, by rw [hq]; exact hi, Or.inr (Or.inl hRi)⟩
      · obtain ⟨i, hi, hRi⟩ := hreg (3, 128) (by simp) e he128
        have hTK : IsInK tabs := (hT 0 (by decide)).1
        refine ⟨i, ?_, Or.inr (Or.inl hRi)⟩
        rw [hq, ← hi]
        show (tabs * gen ^ e).limb 0 * Parameters.addressOfIndex 0 =
          tabs.limb 0 * Parameters.addressOfIndex e
        rw [gen_pow_eq_ofK, limb0_mul_ofK hTK]
        simp [Parameters.addressOfIndex]
    | _ => simp [Ev.loadAddr?] at hA
  · -- the claimed run: the frame's
    obtain ⟨q, hq, hq1, hq2⟩ := hi
    simp only [qwRunL, List.mem_singleton] at hq
    subst hq
    simp only [qwRunList, List.length_map, List.length_range] at hq2
    exact Or.inl (Or.inr ⟨(V.n 5, 36), hrunEs, by show fp + cert name (.n 5) ≤ i; exact hq1,
      by show i < fp + cert name (.n 5) + 36; omega⟩)

end
end LeanVM.Guest.B1
