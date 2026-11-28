/-
  LeanVM.Guest.B1.VsC.CstA

  `check_stack_terminal` completes placed: `CheckStackTerminalCompleteA`.
-/

module

public import LeanVM.Guest.B1.VsC.CstKids
public import LeanVM.Guest.B1.VsC.CstEnd
public import LeanVM.Guest.B1.VsC.CalleesB

/-!
# `check_stack_terminal`, placed

`cst_completeA (11 ≤ k) : CheckStackTerminalCompleteA fs al cert k`, by `callAtA_nodeRd` on
`check_stack_terminal`'s body. Vacuous unless some memory has `StackCtxAt` of the arguments; then the
arguments are `23` words and the layout's facts are fixed. Its ten buffers at its cursor `c` hold
`cstWords`; its callees from `c + 64 (|chi| + 1) + 422`: `stack_selectors__L{(stackLog + 3)/4}`
(`stack_selectors_placed`), `rs_eq_run` (count `h_5 + 6`), `ring_rows`, six `ring_cols`, five
`eq_prefix_chain`, each from the end of the previous. The valuation on each memory is the forward
evaluation with the oracle `cstOrc` (`CstHyp`), `σ0` that on the memory with `StackCtxAt`; the calls'
words agree by `CstG.calls`; every atom holds by `CstHyp.holds` and `CstHyp.assert`.

`cst_completeAE`: the same, its end within `2^24` of its cursor when every frame is below `2^16`
(the callees' ends one after the other: `stack_selectors_placedB`, `rsEnd_le`, `rgEnd_le`,
`epcEnd_le`, `step_le`); `cst_completeAB`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The events of a body of atoms and calls. -/
theorem mem_slEvs_aoc' {σ : Val} : ∀ {ss : List Stmt}, ss.all atomOrCall = true → ∀ {e : Ev},
    e ∈ ss.flatMap (slEvs σ) → (∃ a, e = .atom a ∧ Stmt.atom a ∈ ss) ∨
      ∃ f args rets, e = .call f args rets ∧ Stmt.call f args rets ∈ ss
  | [], _, _, h => by simp at h
  | s :: ss, hs, e, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | atom a => simp only [slEvs, List.mem_singleton] at h; exact Or.inl ⟨a, h, List.mem_cons_self⟩
      | call f args rets =>
        simp only [slEvs, List.mem_singleton] at h; exact Or.inr ⟨f, args, rets, h, List.mem_cons_self⟩
      | _ => simp [atomOrCall] at hs
    · rcases mem_slEvs_aoc' hs.2 h with ⟨a, he, ha⟩ | ⟨f, args, rets, he, hc⟩
      · exact Or.inl ⟨a, he, List.mem_cons_of_mem _ ha⟩
      · exact Or.inr ⟨f, args, rets, he, List.mem_cons_of_mem _ hc⟩

theorem _root_.LeanVM.Guest.Complete.CallAtA.monoPre {fs : String → ℕ} {al : String → Bool}
    {cert : String → V → ℕ} {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop}
    {Out Pre Pre' : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c e : ℕ}
    (h : CallAtA fs al cert k f args rets R D Out Pre Post B fp c e) (hP : ∀ rd, Pre' rd → Pre rd) :
    CallAtA fs al cert k f args rets R D Out Pre' Post B fp c e :=
  h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)

theorem exact_of_plain {rd : Reader} {σ : Val} {a : Atom} (h : cstPlainB a = true) : a.Exact rd σ := by
  cases a with
  | hint hh => cases hh <;> simp_all [cstPlainB, Atom.Exact, Hint.Exact]
  | _ => trivial

theorem quiet_of_plain {a : Atom} (h : cstPlainB a = true) : atomQuiet a = true := by
  cases a with
  | hint hh => cases hh <;> simp_all [cstPlainB, atomQuiet]
  | _ => rfl

theorem hintAddrs_plain {σ : Val} {a : Atom} (h : cstPlainB a = true) : Memory.Ev.hintAddrs σ (.atom a) = [] := by
  have h' : (atomHeapDest? a).isNone = true := by
    simp only [cstPlainB, Bool.and_eq_true] at h; exact h.2
  have := heapHintAddrs_atoms (σ := σ) [a] (by simp [h'])
  simpa [heapHintAddrs] using this

set_option maxHeartbeats 8000000 in
/-- **`check_stack_terminal` completes placed** (`CheckStackTerminalCompleteA`), every `k ≥ 11`, its end
within `2^24` of its cursor when every frame is below `2^16`. -/
theorem cst_completeAE {k : ℕ} (hk : 11 ≤ k) :
    CheckStackTerminalCompleteAE fs al cert k (fun c e => FsSmall fs → e ≤ c + 2 ^ 24) := by
  intro args layout link chi r qPoint kOut kIn f g x z rho lam rm outputs keccakSlices oodValue v0 v1 claims fp
    hcl hL hnat hbelow
  by_cases hex : ∃ rd, StackCtxAt rd args layout link chi r qPoint kOut kIn f g x z rho lam rm outputs
  swap
  · exact ⟨fp + fs "check_stack_terminal", fun _ => Nat.le_add_right _ _, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl,
      fun _ _ => trivial,
      fun rd _ _ hP => absurd ⟨rd, hP⟩ hex⟩
  obtain ⟨rd0, h0⟩ := hex
  obtain ⟨τ, rfl⟩ := args_eq_cstArgsOf (stackCtxAt_length h0)
  have h0' := h0
  obtain ⟨⟨bytecode, rows, hbl⟩, -, -, ⟨h4, -⟩, -, hgn, hchi24, hheights, -, -, -, -, -, hlmr, hglm, -, -, -, -, -,
    -, -, hkoutl, hkinl, hf, hg, -, -, -, hxl, -, -, hzl, -⟩ := h0'
  -- the layout's numbers
  set n := chi.length with hn
  have hn24 : n ≤ 24 := hchi24
  have h5n : hgt layout 5 ≤ n := hheights 5 (by decide)
  have hq6 : hgt layout 5 + 6 ≤ layout.stackLog := by
    have := (block_placed hbl (b := 2) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 2) (by decide)).2.1, (blockKap_eq layout).2.2] at this
  have hlmL : layout.logMemory ≤ layout.stackLog := by
    have := (block_placed hbl (b := 0) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 0) (by decide)).2.1, (blockKap_eq layout).1] at this
  have h16 : 16 ≤ layout.stackLog := by rw [(cs_layout hbl hL).2.1]; exact le_max_left _ _
  have hx40 : x.length ≤ 40 := by omega
  have hko : kOut.length = hgt layout 5 + 6 := by rw [hkoutl]; rfl
  have hkin6 : kIn.length = hgt layout 5 + 6 := by rw [hkinl, hko]
  have hcs : (ringCoefficients f g).length = 64 := ringCoefficients_length f g hf hg
  have hT : (cstSizes n).sum = 64 * (n + 1) + 422 := cstSizes_sum n
  -- the places
  set c := fp + fs "check_stack_terminal" with hc
  set T := 64 * (n + 1) + 422 with hTdef
  set j := layout.stackLog - 16 with hj
  have hj15 : j < 15 := by omega
  set nsel := (19 + j) / 4 with hnsel
  have hnsel' : (layout.stackLog + 3) / 4 = nsel := by rw [hnsel, hj]; congr 1; omega
  set sname := "stack_selectors__L" ++ natStr nsel with hsname
  set arrs := cstArrays (cstValArgs τ) chi r kOut kIn f g z with harrs
  set RR : ℕ → Prop := fun i => ptrRegion arrs i ∨ (c ≤ i ∧ i < c + T) with hRR
  have mem : ∀ {p : E} {len : ℕ}, (p, len) ∈ arrs → ∀ {m}, m ≤ len → PtrCells RR p m :=
    fun hq _ hm => cells_arr hbelow hq hm
  have own : ∀ {b e m : ℕ}, c ≤ b → b + e + m ≤ c + T → PtrCells RR (ptrAtV b * gen ^ e) m :=
    fun h1 h2 => cells_own h1 h2
  have own0 : ∀ {b m : ℕ}, c ≤ b → b + m ≤ c + T → PtrCells RR (ptrAtV b) m := fun h1 h2 => cells_own0 h1 h2
  have base : ∀ i, i < 10 → c ≤ cstBase n c i ∧ cstBase n c i + (cstSizes n).getD i 0 ≤ c + T := by
    intro i hi
    interval_cases i <;> simp [cstBase, cstSizes, hTdef] <;> omega
  -- the selectors
  set fp1 := allocBase (al sname) (c + T) with hfp1
  set csel := fp1 + fs sname with hcsel
  have hRsel : StsRegion RR (τ (.n 2)) (τ (.n 3)) (τ (.n 17)) (τ (.n 18)) (τ (.n 0)) := by
    have hoffs := mem (p := τ (.n 2)) (len := nStkBlocks) (by simp [harrs, cstArrays, cstValArgs]) (m := 52)
      (by simp [nStkBlocks, stackBlocks_length])
    have hkaps := mem (p := τ (.n 3)) (len := nStkBlocks) (by simp [harrs, cstArrays, cstValArgs]) (m := 52)
      (by simp [nStkBlocks, stackBlocks_length])
    have hpt := mem (p := τ (.n 17)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (m := 40) le_rfl
    have hpt1 := mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (m := 40) le_rfl
    have hgsq := mem (p := τ (.n 0)) (len := winTabAt + 2 ^ winTabBits) (by simp [harrs, cstArrays, cstValArgs])
      (m := 178) (by decide)
    exact ⟨fun b hb => ⟨hoffs b hb, hkaps b hb⟩, fun i hi => ⟨hpt i hi, hpt1 i hi⟩,
      fun t ht => hgsq (34 + t) (by omega)⟩
  obtain ⟨e1, hb1, hsel⟩ := stack_selectors_placedB (fs := fs) (al := al) (cert := cert) (k := k) (by omega) nsel
    (by omega) (by omega) hbl hL hnsel' hxl (gmv := τ (.n 4)) hRsel fp1 csel le_rfl
  -- `rs_eq_run`
  set cnt := hgt layout 5 + 6 with hcnt
  set fp2 := allocBase (al "rs_eq_run") e1 with hfp2
  set c2 := fp2 + fs "rs_eq_run" with hc2
  set crow := c2 + 64 * rsH cnt with hcrow
  have hrs := rs_eq_run_placed (fs := fs) (al := al) (cert := cert) k (count := cnt) (by omega)
    (z := τ (.n 10) * gen ^ guest_const% QKECCAK_VARS_CAP) (p1 := τ (.n 18)) (seed := τ (.n 12)) (zs := kIn)
    (ps := (padX1 x).take cnt) (cs := ringCoefficients f g) hkin6 (by simp; omega) hcs
    (mem (p := τ (.n 10) * gen ^ 39) (len := kIn.length) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
    (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
    (mem (p := τ (.n 12)) (len := (ringCoefficients f g).length) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
    fp2 c2 le_rfl
  -- `ring_rows`
  set fp3 := allocBase (al "ring_rows") (rsEnd fs al cnt c2) with hfp3
  set c3 := fp3 + fs "ring_rows" with hc3
  have hrr := ring_rows_placed (fs := fs) (al := al) (cert := cert) k (count := n) (by omega)
    (chain := ptrAtV (cstBase n c 0)) (z := τ (.n 5)) (p := τ (.n 18)) (ct := τ (.n 12)) (zs := chi)
    (ps := (padX1 x).take n) (cs := ringCoefficients f g) rfl (by simp; omega) hcs
    (own0 (base 0 (by norm_num)).1 (by have := (base 0 (by norm_num)).2; simpa [cstSizes] using this))
    (mem (p := τ (.n 5)) (len := n) (by simp [harrs, cstArrays, cstValArgs, hn]) le_rfl)
    (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
    (mem (p := τ (.n 12)) (len := (ringCoefficients f g).length) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
    fp3 c3 le_rfl
  -- `ring_cols`, six of them
  have rowC : ∀ t < 6, PtrCells RR (ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout t)) kBits := fun t ht =>
    own (base 0 (by norm_num)).1 (by
      have h1 := (base 0 (by norm_num)).2
      have h2 := hheights t (by simpa [nTables] using ht)
      simp only [cstSizes, List.getD_cons_zero] at h1
      show cstBase n c 0 + 64 * hgt layout t + 64 ≤ c + T
      have : 64 * hgt layout t + 64 ≤ 64 * (n + 1) := by unfold hgt; omega
      omega)
  have sclC : ∀ q0 nt, q0 + nt ≤ 33 → PtrCells RR (ptrAtV (cstBase n c 2) * gen ^ q0) nt := fun q0 nt h =>
    own (base 2 (by norm_num)).1 (by have := (base 2 (by norm_num)).2; simp [cstSizes] at this; omega)
  have mskC : ∀ q0 nt, q0 + nt ≤ 33 → PtrCells RR (ptrAtV (cstBase n c 1) * gen ^ q0) nt := fun q0 nt h =>
    own (base 1 (by norm_num)).1 (by have := (base 1 (by norm_num)).2; simp [cstSizes] at this; omega)
  have sclC0 : PtrCells RR (ptrAtV (cstBase n c 2)) 5 :=
    own0 (base 2 (by norm_num)).1 (by have := (base 2 (by norm_num)).2; simp [cstSizes] at this; omega)
  have mskC0 : PtrCells RR (ptrAtV (cstBase n c 1)) 5 :=
    own0 (base 1 (by norm_num)).1 (by have := (base 1 (by norm_num)).2; simp [cstSizes] at this; omega)
  set c3e := rgEnd fs al n c3 with hc3e
  set fp4 := allocBase (al "ring_cols__L5") c3e with hfp4
  set c4 := fp4 + fs "ring_cols__L5" with hc4
  have rc0 := ring_cols_placed (fs := fs) (al := al) (cert := cert) k (n := 5) (name := "ring_cols__L5") (by decide)
    (row := ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 0)) (scl := ptrAtV (cstBase n c 2))
    (msk := ptrAtV (cstBase n c 1)) (rs := rcRow (ringCoefficients f g) chi x (hgt layout 0))
    (ss := rcScl rho qPoint 0 5) (ms := rcMsk layout x 0 5) (by simp [rcRow, kBits]) (by simp [rcScl, cstRqW])
    (by simp [rcMsk, cstMaskW]) (R := RR) (hptr3 (rowC 0 (by norm_num)) sclC0 mskC0) fp4 c4
  set fp5 := allocBase (al "ring_cols__L5") c4 with hfp5
  set c5 := fp5 + fs "ring_cols__L5" with hc5
  have rc1 := ring_cols_placed (fs := fs) (al := al) (cert := cert) k (n := 5) (name := "ring_cols__L5") (by decide)
    (row := ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 1)) (scl := ptrAtV (cstBase n c 2) * gen ^ 5)
    (msk := ptrAtV (cstBase n c 1) * gen ^ 5) (rs := rcRow (ringCoefficients f g) chi x (hgt layout 1))
    (ss := rcScl rho qPoint 5 5) (ms := rcMsk layout x 5 5) (by simp [rcRow, kBits]) (by simp [rcScl, cstRqW])
    (by simp [rcMsk, cstMaskW]) (R := RR) (hptr3 (rowC 1 (by norm_num)) (sclC 5 5 (by norm_num))
      (mskC 5 5 (by norm_num))) fp5 c5
  set fp6 := allocBase (al "ring_cols__L3") c5 with hfp6
  set c6 := fp6 + fs "ring_cols__L3" with hc6
  have rc2 := ring_cols_placed (fs := fs) (al := al) (cert := cert) k (n := 3) (name := "ring_cols__L3") (by decide)
    (row := ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 2)) (scl := ptrAtV (cstBase n c 2) * gen ^ 10)
    (msk := ptrAtV (cstBase n c 1) * gen ^ 10) (rs := rcRow (ringCoefficients f g) chi x (hgt layout 2))
    (ss := rcScl rho qPoint 10 3) (ms := rcMsk layout x 10 3) (by simp [rcRow, kBits]) (by simp [rcScl, cstRqW])
    (by simp [rcMsk, cstMaskW]) (R := RR) (hptr3 (rowC 2 (by norm_num)) (sclC 10 3 (by norm_num))
      (mskC 10 3 (by norm_num))) fp6 c6
  set fp7 := allocBase (al "ring_cols__L5") c6 with hfp7
  set c7 := fp7 + fs "ring_cols__L5" with hc7
  have rc3 := ring_cols_placed (fs := fs) (al := al) (cert := cert) k (n := 5) (name := "ring_cols__L5") (by decide)
    (row := ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 3)) (scl := ptrAtV (cstBase n c 2) * gen ^ 13)
    (msk := ptrAtV (cstBase n c 1) * gen ^ 13) (rs := rcRow (ringCoefficients f g) chi x (hgt layout 3))
    (ss := rcScl rho qPoint 13 5) (ms := rcMsk layout x 13 5) (by simp [rcRow, kBits]) (by simp [rcScl, cstRqW])
    (by simp [rcMsk, cstMaskW]) (R := RR) (hptr3 (rowC 3 (by norm_num)) (sclC 13 5 (by norm_num))
      (mskC 13 5 (by norm_num))) fp7 c7
  set fp8 := allocBase (al "ring_cols__L5") c7 with hfp8
  set c8 := fp8 + fs "ring_cols__L5" with hc8
  have rc4 := ring_cols_placed (fs := fs) (al := al) (cert := cert) k (n := 5) (name := "ring_cols__L5") (by decide)
    (row := ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 4)) (scl := ptrAtV (cstBase n c 2) * gen ^ 18)
    (msk := ptrAtV (cstBase n c 1) * gen ^ 18) (rs := rcRow (ringCoefficients f g) chi x (hgt layout 4))
    (ss := rcScl rho qPoint 18 5) (ms := rcMsk layout x 18 5) (by simp [rcRow, kBits]) (by simp [rcScl, cstRqW])
    (by simp [rcMsk, cstMaskW]) (R := RR) (hptr3 (rowC 4 (by norm_num)) (sclC 18 5 (by norm_num))
      (mskC 18 5 (by norm_num))) fp8 c8
  set fp9 := allocBase (al "ring_cols__L10") c8 with hfp9
  set c9 := fp9 + fs "ring_cols__L10" with hc9
  have rc5 := ring_cols_placed (fs := fs) (al := al) (cert := cert) k (n := 10) (name := "ring_cols__L10")
    (by decide) (row := ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout 5)) (scl := ptrAtV (cstBase n c 2) * gen ^ 23)
    (msk := ptrAtV (cstBase n c 1) * gen ^ 23) (rs := rcRow (ringCoefficients f g) chi x (hgt layout 5))
    (ss := rcScl rho qPoint 23 10) (ms := rcMsk layout x 23 10) (by simp [rcRow, kBits]) (by simp [rcScl, cstRqW])
    (by simp [rcMsk, cstMaskW]) (R := RR) (hptr3 (rowC 5 (by norm_num)) (sclC 23 10 (by norm_num))
      (mskC 23 10 (by norm_num))) fp9 c9
  -- `eq_prefix_chain`, five of them
  have chainC : ∀ i < 10, ∀ m, m ≤ (cstSizes n).getD i 0 → PtrCells RR (ptrAtV (cstBase n c i)) m :=
    fun i hi m hm => own0 (base i hi).1 (by have := (base i hi).2; omega)
  set fp10 := allocBase (al "eq_prefix_chain") c9 with hfp10
  set c10 := fp10 + fs "eq_prefix_chain" with hc10
  have ep1 := eq_prefix_chain_placed (fs := fs) (al := al) (cert := cert) (by omega : 6 ≤ k) (n := layout.logMemory)
    (by omega) (chain := ptrAtV (cstBase n c 5)) (seed := 1) (a := τ (.n 7)) (b1 := τ (.n 18))
    (as := r.take layout.logMemory) (bs := (padX1 x).take layout.logMemory) (by simp; omega) (by simp; omega)
    (R := RR) (hptr4 (chainC 5 (by norm_num) _ (by simp [cstSizes]; omega))
      (mem (p := τ (.n 7)) (len := r.length) (by simp [harrs, cstArrays, cstValArgs]) hlmr)
      (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))) fp10 c10
  set fp11 := allocBase (al "eq_prefix_chain") (epcEnd fs al layout.logMemory c10) with hfp11
  set c11 := fp11 + fs "eq_prefix_chain" with hc11
  have ep2 := eq_prefix_chain_placed (fs := fs) (al := al) (cert := cert) (by omega : 6 ≤ k) (n := layout.logMemory)
    (by omega) (chain := ptrAtV (cstBase n c 6)) (seed := 1) (a := ptrAtV (cstBase n c 7)) (b1 := τ (.n 18))
    (as := (piW rm).take layout.logMemory) (bs := (padX1 x).take layout.logMemory) (by simp [piW]; omega)
    (by simp; omega) (R := RR) (hptr4 (chainC 6 (by norm_num) _ (by simp [cstSizes]; omega))
      (chainC 7 (by norm_num) _ (by simp [cstSizes]; omega))
      (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))) fp11 c11
  set fp12 := allocBase (al "eq_prefix_chain") (epcEnd fs al layout.logMemory c11) with hfp12
  set c12 := fp12 + fs "eq_prefix_chain" with hc12
  have ep3 := eq_prefix_chain_placed (fs := fs) (al := al) (cert := cert) (by omega : 6 ≤ k) (n := cnt)
    (by omega) (chain := ptrAtV (cstBase n c 4)) (seed := 1) (a := τ (.n 10)) (b1 := τ (.n 18))
    (as := kOut.take cnt) (bs := (padX1 x).take cnt) (by simp; omega) (by simp; omega)
    (R := RR) (hptr4 (chainC 4 (by norm_num) _ (by simp [cstSizes]; omega))
      (mem (p := τ (.n 10)) (len := kOut.length) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
      (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))) fp12 c12
  set fp13 := allocBase (al "eq_prefix_chain") (epcEnd fs al cnt c12) with hfp13
  set c13 := fp13 + fs "eq_prefix_chain" with hc13
  have ep4 := eq_prefix_chain_placed (fs := fs) (al := al) (cert := cert) (by omega : 6 ≤ k) (n := layout.stackLog)
    (by omega) (chain := ptrAtV (cstBase n c 9)) (seed := 1) (a := τ (.n 22)) (b1 := τ (.n 18))
    (as := z.take layout.stackLog) (bs := (padX1 x).take layout.stackLog) (by simp; omega) (by simp; omega)
    (R := RR) (hptr4 (chainC 9 (by norm_num) _ (by simp [cstSizes]; omega))
      (mem (p := τ (.n 22)) (len := z.length) (by simp [harrs, cstArrays, cstValArgs]) (by omega))
      (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))) fp13 c13
  set fp14 := allocBase (al "eq_prefix_chain") (epcEnd fs al layout.stackLog c13) with hfp14
  set c14 := fp14 + fs "eq_prefix_chain" with hc14
  have hub : FsSmall fs → epcEnd fs al n c14 ≤ c + 2 ^ 24 := by
    intro hfs
    have t1 := allocBase_le (al sname) (c + T)
    have t2 := hfs sname
    have t3 := hb1 hfs
    have t4 := step_le hfs (al "rs_eq_run") "rs_eq_run" e1
    have t5 := rsEnd_le (al := al) hfs (count := cnt) (by omega) c2
    have t6 := step_le hfs (al "ring_rows") "ring_rows" (rsEnd fs al cnt c2)
    have t7 := rgEnd_le (al := al) hfs (count := n) (by omega) c3
    have t8 := step_le hfs (al "ring_cols__L5") "ring_cols__L5" c3e
    have t9 := step_le hfs (al "ring_cols__L5") "ring_cols__L5" c4
    have t10 := step_le hfs (al "ring_cols__L3") "ring_cols__L3" c5
    have t11 := step_le hfs (al "ring_cols__L5") "ring_cols__L5" c6
    have t12 := step_le hfs (al "ring_cols__L5") "ring_cols__L5" c7
    have t13 := step_le hfs (al "ring_cols__L10") "ring_cols__L10" c8
    have t14 := step_le hfs (al "eq_prefix_chain") "eq_prefix_chain" c9
    have t15 := epcEnd_le (al := al) hfs layout.logMemory c10
    have t16 := step_le hfs (al "eq_prefix_chain") "eq_prefix_chain" (epcEnd fs al layout.logMemory c10)
    have t17 := epcEnd_le (al := al) hfs layout.logMemory c11
    have t18 := step_le hfs (al "eq_prefix_chain") "eq_prefix_chain" (epcEnd fs al layout.logMemory c11)
    have t19 := epcEnd_le (al := al) hfs cnt c12
    have t20 := step_le hfs (al "eq_prefix_chain") "eq_prefix_chain" (epcEnd fs al cnt c12)
    have t21 := epcEnd_le (al := al) hfs layout.stackLog c13
    have t22 := step_le hfs (al "eq_prefix_chain") "eq_prefix_chain" (epcEnd fs al layout.stackLog c13)
    have t23 := epcEnd_le (al := al) hfs n c14
    omega
  have ep5 := eq_prefix_chain_placed (fs := fs) (al := al) (cert := cert) (by omega : 6 ≤ k) (n := n)
    (by omega) (chain := ptrAtV (cstBase n c 3)) (seed := 1) (a := τ (.n 5)) (b1 := τ (.n 18))
    (as := chi.take n) (bs := (padX1 x).take n) (by simp [hn]) (by simp; omega)
    (R := RR) (hptr4 (chainC 3 (by norm_num) _ (by simp [cstSizes]; omega))
      (mem (p := τ (.n 5)) (len := chi.length) (by simp [harrs, cstArrays, cstValArgs]) le_rfl)
      (mem (p := τ (.n 18)) (len := 40) (by simp [harrs, cstArrays, cstValArgs]) (by omega))) fp14 c14
  -- the valuation before the memory
  set w := cstOrc layout chi x f g qPoint rho c csel crow with hw
  have rets7 : ∀ σ : Val, (∀ cl ∈ cstRestCalls, ∀ v ∈ cl.rets, σ v = w v.idx) →
      ∀ v ∈ [59, 471, 488, 504, 522, 540, 569], σ (.n v) = w v := by
    intro σ h v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h ⟨"rs_eq_run", [.n 56, .n 18, .n 58, .n 12], [.n 59], true⟩ (by simp [cstRestCalls]) _ (by simp)
    · exact h ⟨"ring_cols__L5", [.n 470, .n 33, .n 32], [.n 471], true⟩ (by simp [cstRestCalls]) _ (by simp)
    · exact h ⟨"ring_cols__L5", [.n 483, .n 485, .n 487], [.n 488], true⟩ (by simp [cstRestCalls]) _ (by simp)
    · exact h ⟨"ring_cols__L3", [.n 499, .n 501, .n 503], [.n 504], true⟩ (by simp [cstRestCalls]) _ (by simp)
    · exact h ⟨"ring_cols__L5", [.n 517, .n 519, .n 521], [.n 522], true⟩ (by simp [cstRestCalls]) _ (by simp)
    · exact h ⟨"ring_cols__L5", [.n 535, .n 537, .n 539], [.n 540], true⟩ (by simp [cstRestCalls]) _ (by simp)
    · exact h ⟨"ring_cols__L10", [.n 564, .n 566, .n 568], [.n 569], true⟩ (by simp [cstRestCalls]) _ (by simp)
  have hw59 : w 59 = ptrAtV crow := by simp [hw, cstOrc]
  have hwrc : ∀ p ∈ rcTab, w p.2.2.2 = rcSum layout chi x f g qPoint rho p.1 p.2.1 p.2.2.1 :=
    fun p hp => cstOrc_rc p hp
  have hw471 : w 471 = rcSum layout chi x f g qPoint rho 0 0 5 := hwrc (0, 0, 5, 471) (by simp [rcTab])
  have hw488 : w 488 = rcSum layout chi x f g qPoint rho 1 5 5 := hwrc (1, 5, 5, 488) (by simp [rcTab])
  have hw504 : w 504 = rcSum layout chi x f g qPoint rho 2 10 3 := hwrc (2, 10, 3, 504) (by simp [rcTab])
  have hw522 : w 522 = rcSum layout chi x f g qPoint rho 3 13 5 := hwrc (3, 13, 5, 522) (by simp [rcTab])
  have hw540 : w 540 = rcSum layout chi x f g qPoint rho 4 18 5 := hwrc (4, 18, 5, 540) (by simp [rcTab])
  have hw569 : w 569 = rcSum layout chi x f g qPoint rho 5 23 10 := hwrc (5, 23, 10, 569) (by simp [rcTab])
  obtain ⟨hG0, hargs0, h43_0, hret0, -⟩ := cst_fwdG (rd := rd0) (c := c) (csel := csel) (crow := crow) h0 hL
  set σ0 := fwdVal rd0 w (cstValArgs τ) cstBody with hσ0
  have parOf : ∀ σ : Val, cstValArgs σ = cstValArgs τ → ∀ i < 23, σ (.n i) = τ (.n i) := fun σ h i hi => by
    have := congrArg (fun l => l.getD i 0) h
    simpa only [cstArgsOf_getD _ hi] using this
  have hp0 := parOf σ0 hargs0
  set es := (cstPreJ j).flatMap (slEvs σ0) with hes
  have hesσ : ∀ σ : Val, (cstPreJ j).flatMap (slEvs σ) = es := fun σ =>
    List.flatMap_congr fun s hs => slEvs_atomOrCall σ σ0 s (List.all_eq_true.mp (cstPreJ_aoc j) s hs)
  have hparts0 := cst_parts σ0 j hG0.v30 hn24
  have hcalls : calls es = ⟨sname, cstArgsV, [.n 43], true⟩ :: cstRestCalls := cst_calls σ0 hj15
  have hcv := hG0.calls (rets7 σ0 hret0)
  rw [hargs0, ← hw] at hcv
  simp only [cstRestCalls, cstCallsV, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    cstArgsOf_getD τ (show 4 < 23 by norm_num), cstArgsOf_getD τ (show 5 < 23 by norm_num),
    cstArgsOf_getD τ (show 6 < 23 by norm_num), cstArgsOf_getD τ (show 7 < 23 by norm_num),
    cstArgsOf_getD τ (show 8 < 23 by norm_num), cstArgsOf_getD τ (show 10 < 23 by norm_num),
    cstArgsOf_getD τ (show 12 < 23 by norm_num), cstArgsOf_getD τ (show 18 < 23 by norm_num),
    cstArgsOf_getD τ (show 22 < 23 by norm_num), hglm, hgn, h4, hw59, hw471, hw488, hw504, hw522, hw540,
    hw569] at hcv
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13⟩ := hcv
  have hRR : ∀ i, RR i → ptrRegion arrs i ∨ ownData cert fp c "check_stack_terminal" (allocs σ0 es) es i :=
    fun i hi => hi.imp id fun h => Or.inl (bufs_cover _ c i h.1 (by rw [hparts0.1, hT]; exact h.2))
  have hwalk : ∀ σ : Val, σ (.n 42) = ofK (addressOfIndex j) →
      walk σ (fn% «check_stack_terminal»).body = .ret es [] := fun σ h42 => by
    rw [check_stack_terminal_body, walk_cst σ hj15 h42, hesσ]
  refine ⟨epcEnd fs al n c14, hub, callAtA_nodeRd cst_loop le_rfl ⟨σ0, fn% «check_stack_terminal», es, [],
    cstWords c layout chi r qPoint kOut x z f g rho rm, List.replicate 14 PostQuiet,
    fun rd => HoldsWords rd (cstWords c layout chi r qPoint kOut x z f g rho rm) ∧
      (∀ b < 52, LoadHolds rd (ofK (addressOfIndex csel)) b (selW layout x b)) ∧
      RsOut (ringCoefficients f g) kIn ((padX1 x).take cnt) (ptrAt crow) rd,
    fun i => (csel ≤ i ∧ i < csel + 52) ∨ (crow ≤ i ∧ i < crow + 64),
    find_cst, ?_, fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩⟩
  · rw [hparts0.1]
    exact cst_wordsInA (by omega) (by omega) (by omega) (by omega) _ _ c
  · -- the callees
    rw [hcalls]
    have hcur : c + (allocs σ0 es).sum = c + T := by rw [hparts0.1, hT]
    rw [hcur]
    refine kidsAtF_take' rfl (as := [τ (.n 2), τ (.n 3), τ (.n 17), τ (.n 18), τ (.n 0)])
      (rs := [ofK (addressOfIndex csel)])
      (by simp only [cstArgsV, List.map_cons, List.map_nil, hp0 2 (by norm_num), hp0 3 (by norm_num),
        hp0 17 (by norm_num), hp0 18 (by norm_num), hp0 0 (by norm_num)])
      (by simp only [List.map_cons, List.map_nil, h43_0]) (fun i hi => Or.inl (hRR i hi))
      (hsel.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, hexp, -, hplaced, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, -, -, hpt, hpt1, -⟩ := h.1
      exact ⟨hplaced, hexp, hpt, hpt1⟩
    refine kidsAtF_take' rfl (Prod.mk.inj q1).1 (Prod.mk.inj q1).2 (fun i hi => Or.inl (hRR i hi))
      (hrs.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkin, -, -, -, -, -, hct,
        -, -, -, -, hpt1, -⟩ := h.1
      exact ⟨hkin, readsAt_take' hpt1 _, hct⟩
    refine kidsAtF_take' rfl (Prod.mk.inj q2).1 (Prod.mk.inj q2).2 (fun i hi => Or.inl (hRR i hi))
      (hrr.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, hchiR, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        hct, -, -, -, -, hpt1, -⟩ := h.1
      exact ⟨hct, hchiR, readsAt_take' hpt1 _, wo0 h.2.1.1⟩
    have rcPre : ∀ rd t q0 nt, t < 6 → q0 + nt ≤ 33 →
        HoldsWords rd (cstWords c layout chi r qPoint kOut x z f g rho rm) →
        ReadsAt rd (ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout t))
          (rcRow (ringCoefficients f g) chi x (hgt layout t)) ∧
        ReadsAt rd (ptrAtV (cstBase n c 2) * gen ^ q0) (rcScl rho qPoint q0 nt) ∧
        ReadsAt rd (ptrAtV (cstBase n c 1) * gen ^ q0) (rcMsk layout x q0 nt) := fun rd t q0 nt ht hq hW =>
      ⟨wo_row hW (hheights t (by simpa [nTables] using ht)),
        readsAt_dropTake (wo_run hW (i := 2) (by simp [cstWords])) (by simp [cstRqW]; omega),
        readsAt_dropTake (wo_run hW (i := 1) (by simp [cstWords])) (by simp [cstMaskW]; omega)⟩
    refine kidsAtF_take' rfl (Prod.mk.inj q3).1 (Prod.mk.inj q3).2 (fun i hi => Or.inl (hRR i hi))
      (rc0.monoPre fun rd h => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := rcPre rd 0 0 5 (by norm_num) (by norm_num) h.2.1.1.1
      rw [pow_zero, mul_one] at h2 h3
      exact ⟨h1, h2, h3⟩
    refine kidsAtF_take' rfl (Prod.mk.inj q4).1 (Prod.mk.inj q4).2 (fun i hi => Or.inl (hRR i hi))
      (rc1.monoPre fun rd h => rcPre rd 1 5 5 (by norm_num) (by norm_num) h.2.1.1.1.1) ?_
    refine kidsAtF_take' rfl (Prod.mk.inj q5).1 (Prod.mk.inj q5).2 (fun i hi => Or.inl (hRR i hi))
      (rc2.monoPre fun rd h => rcPre rd 2 10 3 (by norm_num) (by norm_num) h.2.1.1.1.1.1) ?_
    refine kidsAtF_take' rfl (Prod.mk.inj q6).1 (Prod.mk.inj q6).2 (fun i hi => Or.inl (hRR i hi))
      (rc3.monoPre fun rd h => rcPre rd 3 13 5 (by norm_num) (by norm_num) h.2.1.1.1.1.1.1) ?_
    refine kidsAtF_take' rfl (Prod.mk.inj q7).1 (Prod.mk.inj q7).2 (fun i hi => Or.inl (hRR i hi))
      (rc4.monoPre fun rd h => rcPre rd 4 18 5 (by norm_num) (by norm_num) h.2.1.1.1.1.1.1.1) ?_
    refine kidsAtF_take' rfl (Prod.mk.inj q8).1 (Prod.mk.inj q8).2 (fun i hi => Or.inl (hRR i hi))
      (rc5.monoPre fun rd h => rcPre rd 5 23 10 (by norm_num) (by norm_num) h.2.1.1.1.1.1.1.1.1) ?_
    refine kidsAtF_take' rfl (Prod.mk.inj q9).1 (Prod.mk.inj q9).2 (fun i hi => Or.inl (hRR i hi))
      (ep1.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hrR, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, hpt1, -⟩ := h.1
      exact epc_pre (wo_run h.2.1.1.1.1.1.1.1.1.1 (i := 5) (ws := chainW r x layout.logMemory) (by simp [cstWords]))
        hrR hpt1
    refine kidsAtF_take' rfl (Prod.mk.inj q10).1 (Prod.mk.inj q10).2 (fun i hi => Or.inl (hRR i hi))
      (ep2.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, hpt1, -⟩ := h.1
      have hW := h.2.1.1.1.1.1.1.1.1.1.1
      exact epc_pre (wo_run hW (i := 6) (ws := chainW (piW rm) x layout.logMemory) (by simp [cstWords]))
        (wo_run hW (i := 7) (ws := piW rm) (by simp [cstWords])) hpt1
    refine kidsAtF_take' rfl (Prod.mk.inj q11).1 (Prod.mk.inj q11).2 (fun i hi => Or.inl (hRR i hi))
      (ep3.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzv, -, -, -, -, -, -, -, -,
        -, -, -, hpt1, -⟩ := h.1
      have hW := h.2.1.1.1.1.1.1.1.1.1.1.1
      have hc4 := wo_run hW (i := 4) (ws := chainW kOut x kOut.length) (by simp [cstWords])
      rw [hko] at hc4
      exact epc_pre hc4 hzv hpt1
    refine kidsAtF_take' rfl (Prod.mk.inj q12).1 (Prod.mk.inj q12).2 (fun i hi => Or.inl (hRR i hi))
      (ep4.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, hpt1, -, hoodz⟩ := h.1
      have hW := h.2.1.1.1.1.1.1.1.1.1.1.1.1
      have hc9 := wo_run hW (i := 9) (ws := chainW z x z.length) (by simp [cstWords])
      rw [hzl] at hc9
      exact epc_pre hc9 hoodz hpt1
    refine kidsAtF_take' rfl (Prod.mk.inj q13).1 (Prod.mk.inj q13).2 (fun i hi => Or.inl (hRR i hi))
      (ep5.monoPre fun rd h => ?_) ?_
    · obtain ⟨-, -, -, -, hchiR, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, -, hpt1, -⟩ := h.1
      have hW := h.2.1.1.1.1.1.1.1.1.1.1.1.1.1
      exact epc_pre (wo_run hW (i := 3) (ws := chainW chi x chi.length) (by simp [cstWords])) hchiR hpt1
    refine ⟨rfl, fun rd h => ?_, fun i hi => ?_⟩
    · simp only [and_true] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · simp only [or_false, false_or]
      exact hi
  · -- on a memory
    intro rd hl hp ho
    obtain ⟨hW, hselO, hrsO⟩ := ho
    obtain ⟨hG, hargs, h43, hret, hgs⟩ := cst_fwdG (rd := rd) (c := c) (csel := csel) (crow := crow) hp hL
    set σ := fwdVal rd w (cstValArgs τ) cstBody with hσ
    have hpσ := parOf σ hargs
    have hrets := rets7 σ hret
    have h59 : σ (.n 59) = ptrAtV crow := (hrets 59 (by simp)).trans hw59
    have hH : CstHyp rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c csel crow fp :=
      ⟨fun a ha => hgs _ ha, hG.buf, h43, h59, hG.ctx, hL, by rw [hargs]; exact hbelow, hW, hselO,
        fun j hj => ⟨_, hrsO j hj⟩⟩
    have hrc : ∀ p ∈ rcTab, σ (.n p.2.2.2) = rcSum layout chi x f g qPoint rho p.1 p.2.1 p.2.2.1 := by
      intro p hp'
      refine (hrets _ ?_).trans (hwrc p hp')
      simp only [rcTab, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hnat' : (σ (.n 19) + stackedBasis claims lam x) * σ (.n 20) = σ (.n 21) := by
      rw [hpσ 19 (by norm_num), hpσ 20 (by norm_num), hpσ 21 (by norm_num)]
      simpa only [cstArgsOf_getD τ (show 19 < 23 by norm_num), cstArgsOf_getD τ (show 20 < 23 by norm_num),
        cstArgsOf_getD τ (show 21 < 23 by norm_num)] using hnat
    have hesσ' := hesσ σ
    refine ⟨σ, by rw [cst_params]; exact hargs, hwalk σ hG.v42, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have a1 := (cst_parts σ j hG.v30 hn24).1
      rw [hesσ'] at a1
      rw [a1, hparts0.1]
    · refine ⟨?_, by rw [hparts0.2.2]; simp⟩
      rw [hparts0.2.1, hparts0.1, bases_cst, List.map_map, List.map_map]
      refine List.map_congr_left fun i hi => ?_
      simp only [Function.comp_apply]
      exact hG.buf i (List.mem_range.mp hi)
    · rw [hcalls]
      intro cl hcl
      rcases List.mem_cons.mp hcl with rfl | hcl
      · refine ⟨?_, ?_⟩
        · simp only [cstArgsV, List.map_cons, List.map_nil, hp0 2 (by norm_num), hp0 3 (by norm_num),
            hp0 17 (by norm_num), hp0 18 (by norm_num), hp0 0 (by norm_num), hpσ 2 (by norm_num),
            hpσ 3 (by norm_num), hpσ 17 (by norm_num), hpσ 18 (by norm_num), hpσ 0 (by norm_num)]
        · simp only [List.map_cons, List.map_nil, h43_0, h43]
      · have e0 := hG0.calls (rets7 σ0 hret0)
        have e1 := hG.calls hrets
        rw [hargs0] at e0
        rw [hargs] at e1
        exact Prod.mk.inj (List.map_inj_left.mp (e0.trans e1.symm) cl hcl)
    · intro A hA
      rw [loadAddrs, List.mem_filterMap] at hA
      obtain ⟨ev, hev, hA⟩ := hA
      rw [← hesσ'] at hev
      rcases mem_slEvs_aoc' (cstPreJ_aoc j) hev with ⟨a, rfl, ha⟩ | ⟨f', a1, r1, rfl, -⟩
      · cases a with
        | load d p off =>
          simp only [Memory.Ev.loadAddr?, Option.some.injEq] at hA
          subst hA
          rcases mem_B_of_preJ ha with hB | hB
          · obtain ⟨i, hi, hloc⟩ := (hH.load (mem_atomsB hB)).1
            refine ⟨i, hi, ?_⟩
            rw [hargs] at hloc
            rcases hloc with h1 | h1 | h1 | h1
            · exact Or.inl (Or.inl (bufs_cover _ c i h1.1 (by rw [hparts0.1, hT]; exact h1.2)))
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr (Or.inl h1))
            · exact Or.inr (Or.inr (Or.inr h1))
          · cases hB
        | _ => simp [Memory.Ev.loadAddr?] at hA
      · simp [Memory.Ev.loadAddr?] at hA
    · intro A hA
      rw [heapHintAddrs, List.mem_flatMap] at hA
      obtain ⟨ev, hev, hA⟩ := hA
      rw [← hesσ'] at hev
      rcases mem_slEvs_aoc' (cstPreJ_aoc j) hev with ⟨a, rfl, ha⟩ | ⟨f', a1, r1, rfl, -⟩
      · rw [hintAddrs_plain (cst_plain_preJ ha)] at hA
        exact absurd hA List.not_mem_nil
      · simp [Memory.Ev.hintAddrs] at hA
    · intro ev hev
      rw [← hesσ'] at hev
      rcases mem_slEvs_aoc' (cstPreJ_aoc j) hev with ⟨a, rfl, ha⟩ | ⟨f', a1, r1, rfl, -⟩
      · rcases mem_B_of_preJ ha with hB | rfl
        · exact hH.holds a (mem_atomsB hB)
        · exact hH.assert hrsO hrc hcl hnat'
      · trivial
    · intro ts hv hq
      refine postQuiet_node find_cst (hwalk σ hG.v42) (fun a ha => ?_) (fun e he => ?_) hv ?_ _
      · rw [← hesσ'] at ha
        rcases mem_slEvs_aoc' (cstPreJ_aoc j) ha with ⟨a', he, ha'⟩ | ⟨f', a1, r1, he, -⟩
        · cases he; exact quiet_of_plain (cst_plain_preJ ha')
        · cases he
      · rw [← hesσ'] at he
        rcases mem_slEvs_aoc' (cstPreJ_aoc j) he with ⟨a', rfl, ha'⟩ | ⟨f', a1, r1, rfl, -⟩
        · exact exact_of_plain (cst_plain_preJ ha')
        · trivial
      · rw [hcalls] at hq ⊢
        exact hq

/-- **`check_stack_terminal` completes placed** (`CheckStackTerminalCompleteA`), every `k ≥ 11`. -/
theorem cst_completeA {k : ℕ} (hk : 11 ≤ k) : CheckStackTerminalCompleteA fs al cert k :=
  (cst_completeAE hk).toA

/-- **`check_stack_terminal` completes placed, its end within `2^24` of its cursor**, every frame
below `2^16`. -/
theorem cst_completeAB {k : ℕ} (hk : 11 ≤ k) (hfs : FsSmall fs) : CheckStackTerminalCompleteAB fs al cert k 24 :=
  (cst_completeAE hk).mono fun _ _ h _ => h hfs

end
end LeanVM.Guest.B1.VsC
