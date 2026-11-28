module

public import LeanVM.Guest.Complete.DaLevelsA
public import LeanVM.Guest.Complete.DaLoop
public import LeanVM.Guest.Complete.KidsA
public import LeanVM.Guest.Complete.DaWords
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_cell»
import LeanVM.Guest.Data.ValNames.«da_verify_blob»
import LeanVM.Guest.Data.ValNames.«da_verify_blob_loop0»
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»

/-!
# A blob's check and the blob loop, placed

* `cell_callAtA`: `da_verify_cell` places nothing; on its column's weights at index `q` it loads
  only them (`loadOkHB`: its one hint goes to the stack), by the transfer.
* `blL_callAtA`: the cell loop from `g^h`, each iteration's cell check fresh from the cursor, on
  the weights table at `bw`, column `h`'s run at `bcol h` (`wsWords`) and the blob's region at `bb`
  (`BlobLPreA`), loading in them (`blobLR`).
* `blob_callAtA`: `da_verify_blob` at frame `fp` and cursor `c`, its region its own words at `c`,
  its cell loop and its tree's levels (`dl_callAtA`) after it.
* `dvL_callAtA`: `da_verify`'s blob loop from `g^i`, each blob's check fresh, its root stored at the
  roots' slot `2i` (`dvLR`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.VsC LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

set_option linter.constructorNameAsVariable false

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## Leaves reading their arguments' arrays, hinting to the stack -/

/-- `loadOkB`, a hint to the stack allowed. -/
def loadOkHB (ps : List (ℕ × ℕ)) : Atom → Bool
  | .hint h => ((hintDest? h).bind destHeap?).isNone
  | a => loadOkB ps a

theorem loadsR_hintsR_of_loadOkH {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {bs : ℕ → ℕ} {args rets : List E}
    {rd : Reader} {t : Tree} (R R' : ℕ → Prop) (hreg : ∀ i, argRegionAt ps bs i → R' i)
    (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkHB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, args.getD q.1 0 = ptrAt (bs q.1))
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram R' ∧ t.HintsR coreProgram R := by
  obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, hpar, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
    rw [hw'] at hw
    cases hw
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = (atomsOf ss).map Ev.atom := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw']
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok : ∀ a ∈ atomsOf ss, loadOkHB ps a = true := fun a ha =>
      List.all_eq_true.mp hL a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)))
    have hσ : ∀ j < args.length, σ (.n j) = args.getD j 0 := by
      intro j hj
      have hj' : (((List.range args.length).map V.n).map σ)[j]? = args[j]? := by rw [← hparams, hpar]
      simp [hj] at hj'
      simpa [List.getD_eq_getElem?_getD, hj] using hj'
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        simp only [loadOkHB, loadOkB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, rfl, hoff⟩ := hk
        refine ⟨bs q.1 + off, ?_, hreg _ ⟨q, hqm, by omega, by omega⟩⟩
        rw [← hA, hσ _ (hargs q hqm), hptr q hqm]
        exact Main.addr_ofK _ off
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | hint h => cases h <;> simp_all [loadOkHB, Ev.hintAddrs, hintDest?, Option.isNone_iff_eq_none]
      | _ => simp [Ev.hintAddrs] at hA

/-! ## The cell check -/

theorem cell_pureIn : coreProgram.PureIn ["da_verify_cell"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_da_verify_cell] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

theorem cell_not_loop : coreProgram.loop "da_verify_cell" = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem cell_loadOk : (atomsOf (fn% «da_verify_cell»).body).all (loadOkHB [(0, 128)]) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell_ret : (retOf (fn% «da_verify_cell»).body).isSome = true := by decide +kernel

theorem cell_noCalls (fn : Fn) (σ : Val) (es : List Ev) (vs : List V)
    (hf : coreProgram.find? "da_verify_cell" = some fn) (hw : walk σ fn.body = .ret es vs) : calls es = [] := by
  rw [find_da_verify_cell] at hf
  obtain rfl := Option.some.inj hf
  obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp cell_ret
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hb' : (fn% «da_verify_cell»).body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by
    rw [hbody, ← eq_map_atomsOf hss]
  rw [hb', walk_atoms] at hw
  cases hw
  exact calls_atoms _

/-- **`da_verify_cell` completes placed** at any frame and cursor, on its column's weights `ws` at
index `q`, loading only them. -/
theorem cell_callAtA (k : ℕ) {q : ℕ} {syms ws : List E} (hsl : syms.length = LeanDa.cellSymbols)
    (hwl : ws.length = LeanDa.cellSymbols) (fp c : ℕ) :
    CallAtA fs al cert k "da_verify_cell" [ptrAt q] (cellRets syms ws) (fun i => q ≤ i ∧ i < q + 128)
      (fun _ => False) (fun _ => True) (fun rd => ReadsAt rd (ptrAt q) ws)
      (fun rd t => t.pops coreProgram rd = [("da_symbols", syms)] ∧ t.Every (ExactAt coreProgram rd))
      (fs "da_verify_cell") fp c c := by
  refine callAtA_of_callCompletes0 cell_pureIn List.mem_cons_self le_rfl
    ((da_verify_cell_completes k (ptrAt q) hsl hwl).exact da_verify_cell_exactFree)
    fun rd t _ _ hn hv hb _ => ?_
  have hbe := block_endA_leaf (fs := fs) (al := al) cell_pureIn List.mem_cons_self cell_not_loop cell_noCalls hn hv hb c
  refine ⟨hbe.1, hbe.2, loadsR_hintsR_of_loadOkH (bs := fun _ => q) _ _ (fun i ⟨qq, hqq, h1, h2⟩ => ?_)
    find_da_verify_cell rfl cell_loadOk cell_ret (by simp) (by simp) hn hv⟩
  simp only [List.mem_singleton] at hqq
  subst hqq
  exact ⟨h1, h2⟩

/-! ## The weights, placed -/

/-- **The weights table at `bw` and the columns' runs**: column `h`'s pointer `g^(bcol h + 128)`,
its leaves its weights. -/
theorem weightsAt_of {rd : Reader} {z : E} {bw : ℕ} {bcol : ℕ → ℕ} (h : HoldsWords rd (wsWords z bw bcol))
    {c : ℕ} (hc : c < 128) :
    LoadHolds rd (ptrAt bw * gen ^ c) 0 (ptrAt (bcol c + 128)) ∧ ReadsAt rd (ptrAt (bcol c + 128)) (colWs z c) := by
  rw [wsWords, holdsWords_cons] at h
  have e1 : ptrAt bw = gen ^ bw := (gen_pow_eq_ofK bw).symm
  have e2 : ptrAt (bcol c + 128) = gen ^ (bcol c + 128) := (gen_pow_eq_ofK _).symm
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · have := h.1 c (by simp [wsTable]; omega)
    rw [loadHolds_mul_gen_pow, Nat.add_zero]
    simpa [wsTable] using this
  · have hr : ReadsAt rd (gen ^ bcol c) (colRun z c) := by
      have := h.2 (bcol c, colRun z c) (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
      rwa [← gen_pow_eq_ofK] at this
    rw [pow_add]
    refine readsAt_sub hr (by simp [colWs]) fun i hi => ?_
    simp only [colWs, List.length_map, List.length_range] at hi
    rw [colRun_leaf z c hi, colWs, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
      List.getElem_range]

/-- The weights' cells: the table at `bw`, column `h`'s run at `bcol h`. -/
def wsR (bw : ℕ) (bcol : ℕ → ℕ) (i : ℕ) : Prop :=
  (bw ≤ i ∧ i < bw + 128) ∨ ∃ h < 128, bcol h ≤ i ∧ i < bcol h + 256

/-! ## The cell loop -/

/-- What the cell loop reads: the weights and the blob's region at `bb`. -/
def BlobLPreA (z : E) (syms : ℕ → List E) (bw : ℕ) (bcol : ℕ → ℕ) (bb : ℕ) (rd : Reader) : Prop :=
  HoldsWords rd (wsWords z bw bcol) ∧ ReadsAt rd (ptrAt bb) (blobRegion z syms)

/-- The cells the cell loop reads and writes. -/
def blobLR (bw : ℕ) (bcol : ℕ → ℕ) (bb : ℕ) (i : ℕ) : Prop := wsR bw bcol i ∨ (bb ≤ i ∧ i < bb + 641)

theorem blL_loop : coreProgram.loop name% «da_verify_blob_loop0» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem blL_step_A (hfs : ∀ g, fs g < 2 ^ 16) (k : ℕ) (z : E) {syms : ℕ → List E}
    (hsl : ∀ h, (syms h).length = LeanDa.cellSymbols)
    {bw : ℕ} {bcol : ℕ → ℕ} {bb : ℕ} {h : ℕ} (hh : h < 128) {fp c : ℕ}
    (hfc : fp + lpBlk fs name% «da_verify_blob_loop0» (128 - h) ≤ c)
    (htail : h + 1 < 128 → ∀ fp' c', fp' + lpBlk fs name% «da_verify_blob_loop0» (128 - (h + 1)) ≤ c' → ∃ e,
      e ≤ c' + (128 - (h + 1)) * 2 ^ 17 ∧ CallAtA fs al cert k name% «da_verify_blob_loop0» [gen ^ (h + 1), ptrAt bw, ptrAt bb] [] (blobLR bw bcol bb)
        (fun _ => False) (fun _ => True) (BlobLPreA z syms bw bcol bb) (BlobLPost syms (h + 1))
        (lpBlk fs name% «da_verify_blob_loop0» (128 - (h + 1))) fp' c' e) :
    ∃ e, e ≤ c + (128 - h) * 2 ^ 17 ∧
      CallAtA fs al cert k name% «da_verify_blob_loop0» [gen ^ h, ptrAt bw, ptrAt bb] [] (blobLR bw bcol bb)
      (fun _ => False) (fun _ => True) (BlobLPreA z syms bw bcol bb) (BlobLPost syms h)
      (lpBlk fs name% «da_verify_blob_loop0» (128 - h)) fp c e := by
  set L := name% «da_verify_blob_loop0»
  set σ := blLσ (ptrAt bw) (ptrAt bb) (ptrAt (bcol h + 128)) (cellRets (syms h) (colWs z h)) (runSum z syms h) h
    with hσ
  have hblk : lpBlk fs L (128 - h) = fs L + lpBlk fs L (128 - (h + 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, 128 - h = m + 1 := ⟨127 - h, by omega⟩
    rw [lpBlk, lpBlk, hm, show 128 - (h + 1) = m by omega, Nat.add_mul, one_mul]; ring
  rw [hblk] at hfc ⊢
  have e16 : σ (.n 16) = gen ^ (h + 1) + gen ^ 128 := by
    show gen ^ h * word 2 0 + word 325 0 = _; rw [gen_mul_two, word_g128]
  have hargs : [V.n 18, .n 1, .n 2].map σ = [gen ^ (h + 1), ptrAt bw, ptrAt bb] := by
    show [gen ^ h * word 2 0, ptrAt bw, ptrAt bb] = _; rw [gen_mul_two]
  have hcalls : (blLPre.filterMap Stmt.callS).map (mkCall σ) =
      [⟨"da_verify_cell", [.n 4], [.n 5, .n 6, .n 7], true⟩,
        ⟨L, [.n 18, .n 1, .n 2], [], decide (σ (.n 16) ≠ 0)⟩] := rfl
  set ccur := allocBase (al "da_verify_cell") c + fs "da_verify_cell" with hccur
  have hcell := cell_callAtA (fs := fs) (al := al) (cert := cert) k (q := bcol h + 128) (hsl h) (length_colWs z h)
    (allocBase (al "da_verify_cell") c) ccur
  -- the tail, from the cell's end
  have htl : ∃ e Bt, Bt = lpBlk fs L (128 - (h + 1)) ∧ e ≤ ccur + (128 - (h + 1)) * 2 ^ 17 ∧ KidsAtL fs al cert k σ
      (blobLR bw bcol bb) (BlobLPreA z syms bw bcol bb) (fp + fs L) (fun rd => HoldsWords rd [] ∧ True) (fun i => False ∨ False)
      [BlobLPost syms (h + 1)] [⟨L, [.n 18, .n 1, .n 2], [], decide (σ (.n 16) ≠ 0)⟩] ccur e Bt
      (fun rd => HoldsWords rd []) (fun _ => False) := by
    by_cases hlt : h + 1 < 128
    · have htk : decide (σ (.n 16) ≠ 0) = true := by
        rw [e16, gen_guard (by norm_num) (by omega)]; exact decide_eq_true (by omega)
      obtain ⟨e, heb, he⟩ := htail hlt (fp + fs L) ccur (by
        have := le_allocBase (al "da_verify_cell") c; omega)
      refine ⟨e, _, rfl, heb, ?_⟩
      rw [KidsAtL]
      simp only [htk, ↓reduceIte]
      refine ⟨blobLR bw bcol bb, fun _ => False, fun _ => True, fun i hi => Or.inl hi, ?_,
        fun _ h _ => h.1, fun _ h => h.elim⟩
      rw [hargs]
      exact he.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h)
    · have htk : decide (σ (.n 16) ≠ 0) = false := by
        rw [e16, gen_guard (by norm_num) (by omega)]; exact decide_eq_false (by omega)
      refine ⟨ccur, _, rfl, by omega, ?_⟩
      rw [KidsAtL]
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨blLσ (ptrAt bw) (ptrAt bb) 0 [] 0 (h + 1), fn% «da_verify_blob_loop0», find_blL, ?_⟩, ?_, trivial, fun _ h => h.1,
        fun _ h => h.elim⟩
      · rw [blL_params, hargs]; rfl
      · rw [show 128 - (h + 1) = 0 by omega, lpBlk]; simp
  obtain ⟨e, Bt, rfl, heb, htl⟩ := htl
  refine ⟨e, ?_, callAtA_straightL find_blL blL_body rfl (by decide +kernel) blL_loop hfc σ rfl rfl ?_
    [fun rd t => t.pops coreProgram rd = [("da_symbols", syms h)] ∧ t.Every (ExactAt coreProgram rd),
      BlobLPost syms (h + 1)]
    (fun rd => HoldsWords rd []) (fun _ => False) ?_ (fun _ _ => trivial) ?_ ?_⟩
  · have h1 := allocBase_le (al "da_verify_cell") c
    have h2 := hfs "da_verify_cell"
    omega
  · intro x hx
    simp only [blLPre, List.filterMap_cons, stmtLoad?, List.filterMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨bw + h + 0, by show (ptrAt bw * gen ^ h).limb 0 * _ = _; rw [ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inl (Or.inl ⟨by omega, by omega⟩)⟩
    · exact ⟨bb + h + 512, by show (ptrAt bb * gen ^ h).limb 0 * _ = _; rw [ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨bb + h + 513, by show (ptrAt bb * gen ^ h).limb 0 * _ = _; rw [ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨bb + 2 * h + 0, by
        show (ptrAt bb * (gen ^ h * gen ^ h)).limb 0 * _ = _; rw [gen_sq, ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨bb + 2 * h + 1, by
        show (ptrAt bb * (gen ^ h * gen ^ h)).limb 0 * _ = _; rw [gen_sq, ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inr ⟨by omega, by omega⟩⟩
  · rw [hcalls, KidsAtL]
    simp only [↓reduceIte]
    refine ⟨fs "da_verify_cell", ccur, fun i => bcol h + 128 ≤ i ∧ i < bcol h + 128 + 128, fun _ => False,
      fun _ => True, fun i hi => Or.inl (Or.inl (Or.inr ⟨h, hh, by omega, by omega⟩)), ?_, htl⟩
    exact hcell.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
      (fun rd hp => (weightsAt_of hp.1.1 hh).2) (fun _ _ _ h => h)
  · intro rd _ hp _ s hs
    obtain ⟨hW, hR⟩ := hp
    obtain ⟨hlv, -⟩ := weightsAt_of hW hh
    have hreg := fun i hi => loadHolds_of_readsAt hR (i := i) (by rw [length_blobRegion]; exact hi)
    simp only [blLPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact rfl
    · exact hlv
    · trivial
    · exact rfl
    · show LoadHolds rd (ptrAt bb * gen ^ h) 512 (runSum z syms h)
      rw [loadHolds_mul_gen_pow, ← blobRegion_sum z syms (by omega)]; exact hreg _ (by omega)
    · exact rfl
    · show LoadHolds rd (ptrAt bb * gen ^ h) 513 (runSum z syms h + cellDot z syms h)
      rw [loadHolds_mul_gen_pow, ← runSum_succ, show h + 513 = (h + 1) + 512 by omega,
        ← blobRegion_sum z syms (by omega)]
      exact hreg _ (by omega)
    · exact rfl
    · exact rfl
    · show LoadHolds rd (ptrAt bb * (gen ^ h * gen ^ h)) 0 (digestHalves (cellDig syms h)).1
      rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero, ← (blobRegion_leaf z syms hh).1]
      exact hreg _ (by omega)
    · show LoadHolds rd (ptrAt bb * (gen ^ h * gen ^ h)) 1 (digestHalves (cellDig syms h)).2
      rw [gen_sq, loadHolds_mul_gen_pow, ← (blobRegion_leaf z syms hh).2]
      exact hreg _ (by omega)
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (σ (.n 16)); rw [e16]; exact gen_pow_add_isInK _ _
  · intro rd ts _ _ _ hv hq
    rw [hcalls] at hv hq
    match ts, hv with
    | [tc, t1], hv =>
      have hpc : tc.pops coreProgram rd = [("da_symbols", syms h)] := (kidsPost_cons.mp hq).1 rfl |>.1
      have hp1 : t1.pops coreProgram rd = (List.range' (h + 1) (128 - (h + 1))).map fun j => ("da_symbols", syms j) := by
        by_cases hlt : h + 1 < 128
        · have htk : decide (σ (.n 16) ≠ 0) = true := by
            rw [e16, gen_guard (by norm_num) (by omega)]; exact decide_eq_true (by omega)
          exact (kidsPost_cons.mp (kidsPost_cons.mp hq).2).1 htk
        · have htk : decide (σ (.n 16) ≠ 0) = false := by
            rw [e16, gen_guard (by norm_num) (by omega)]; exact decide_eq_false (by omega)
          have hv2 := hv.2.2.2.1
          simp only [htk, Bool.false_eq_true, ↓reduceIte] at hv2
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv2
          rw [Tree.pops, show 128 - (h + 1) = 0 by omega]; rfl
      show _ = _
      rw [pops_straight_none find_blL blL_body rfl rfl (by rw [hcalls]; exact hv), Tree.popsKids, Tree.popsKids,
        Tree.popsKids, hpc, hp1, show 128 - h = 128 - (h + 1) + 1 by omega, List.range'_succ]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.singleton_append]
    | [], hv => simp [Tree.KidsValid] at hv
    | [_], hv => simp [Tree.KidsValid] at hv
    | _ :: _ :: _ :: _, hv => simp [Tree.KidsValid] at hv

/-- **The cell loop completes placed** from every counter below `128`. -/
theorem blL_callAtA (hfs : ∀ g, fs g < 2 ^ 16) (k : ℕ) (z : E) {syms : ℕ → List E}
    (hsl : ∀ h, (syms h).length = LeanDa.cellSymbols)
    {bw : ℕ} {bcol : ℕ → ℕ} {bb : ℕ} : ∀ h < 128, ∀ fp c, fp + lpBlk fs name% «da_verify_blob_loop0» (128 - h) ≤ c →
      ∃ e, e ≤ c + (128 - h) * 2 ^ 17 ∧ CallAtA fs al cert k name% «da_verify_blob_loop0» [gen ^ h, ptrAt bw, ptrAt bb] [] (blobLR bw bcol bb)
        (fun _ => False) (fun _ => True) (BlobLPreA z syms bw bcol bb) (BlobLPost syms h)
        (lpBlk fs name% «da_verify_blob_loop0» (128 - h)) fp c e := by
  have key : ∀ t h, h + 1 + t = 128 → ∀ fp c, fp + lpBlk fs name% «da_verify_blob_loop0» (128 - h) ≤ c →
      ∃ e, e ≤ c + (128 - h) * 2 ^ 17 ∧ CallAtA fs al cert k name% «da_verify_blob_loop0» [gen ^ h, ptrAt bw, ptrAt bb] [] (blobLR bw bcol bb)
        (fun _ => False) (fun _ => True) (BlobLPreA z syms bw bcol bb) (BlobLPost syms h)
        (lpBlk fs name% «da_verify_blob_loop0» (128 - h)) fp c e := by
    intro t
    induction t with
    | zero => intro h hh fp c hfc; exact blL_step_A hfs k z hsl (by omega) hfc fun h' => absurd h' (by omega)
    | succ t ih => intro h hh fp c hfc; exact blL_step_A hfs k z hsl (by omega) hfc fun _ => ih (h + 1) (by omega)
  intro h hh
  exact key (128 - h - 1) h (by omega)

end
end LeanVM.Guest.Complete
