/-
  LeanVM.Guest.EndExecCoreSt

  The core route's stream-cursor family at the honest instances: a loop's reads past its cursor lie in its
  caller's proof stream (the old route's cursor invariants on names).
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResStB
public import LeanVM.Guest.CoreMode.Fam.ResGkrL
public import LeanVM.Guest.CoreMode.Fam.ResVtB
public import LeanVM.Guest.EndExecCoreMono

/-!
# The stream-cursor family, sound

`st_inst`: at an honest instance of a stream-cursor loop (`stK`: `keccak_layer`'s two loops, `verify_tables`'
rounds loop, `gkr_layer__L{p}_L{o}`'s loop), its header names its caller's frame `a`, whose cell `D` holds the proof
stream; with its ghost words that stream and the frame's address (`setG σ [M (a + D), g^a]`), each read of the
family (`stSub`) lies in the stream: the cursor the body loads from its record is `M (a + D)·g^q` with room for an
iteration's words (`LoopQ`, `VtLQ`, `GlLQ`), so `q + c < 8192` (`stSub_holds`). `stGlF`: its linked cells hold.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes stK stSub GlF setG setG_eq ownG ownG_setG prodW vw capE rep_of
  rep_const idxC baseC valW_baseC)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem setG_ghosts2 (σ : Val) (u w : E) :
    setG σ [u, w] (V.n CoreMode.GB) = u ∧ setG σ [u, w] (V.n (CoreMode.GB + 1)) = w := by
  have h := ownG_setG (G := ({ ghosts := 2 } : CoreMode.HSig)) (σ := σ) (gw := [u, w]) rfl
  simpa [CoreMode.ownG, CoreMode.vw, List.range_succ] using h

theorem setG_ghost0' (σ : Val) (u w : E) : setG σ [u, w] (V.n CoreMode.GB) = u := (setG_ghosts2 σ u w).1

/-- **A read past a stream cursor holds** at the valuation whose first ghost is the stream `M`, the cursor
`σ v = M·g^q` with room for `S` words. -/
theorem stSub_holds {fn : Fn} {D v S : ℕ} (hk : stK fn = some (D, v, S)) (hv : v < CoreMode.GB) {σ : Val}
    {M w : E} {q : ℕ} (hcur : σ (.n v) = M * gen ^ q) (hroom : q + S ≤ 8192) :
    ∀ x, stSub fn x = true → x.Holds (setG σ [M, w]) := by
  intro x hx
  match x, hx with
  | .sub c qr, hx =>
    simp only [stSub, hk, Option.any_some, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hx
    obtain ⟨⟨hcb, hc⟩, rfl⟩ := hx
    show CoreMode.RunSet _ _ _ _ _ _
    refine ⟨0, 8192, q + c.off, rep_const (by unfold capE; omega), rep_const (by unfold capE; omega),
      Nat.zero_le _, by omega, ?_⟩
    have hwg : vw (setG σ [M, w]) CoreMode.GB = M := setG_ghost0' σ M w
    have hwv : vw (setG σ [M, w]) v = σ (.n v) := setG_eq (show (V.n v).idx < CoreMode.GB from hv)
    unfold CoreMode.CCell.addrW CoreMode.CCell.valW
    rw [hcb]
    simp only [prodW, pow_one, mul_one, hwg, hwv, hcur, gen_pow_eq_ofK, one_mul]
    simp only [addressOfIndex, pow_add, pow_zero, LeanVM.Guest.CoreMode.ofK_mul']
    rw [CoreMode.ofK_oneL]
    ring_nf
  | .lt _ _, hx | .nz _, hx | .subR _ _, hx | .under _ _, hx | .subP _ _, hx => simp [stSub] at hx

theorem room_of {q S n j : ℕ} (hjn : j < n) (h : q + S * (n - j) ≤ 8192) : q + S ≤ 8192 := by
  have : S ≤ S * (n - j) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The rounds loop's atoms, on its core function: the record `rounds·x^7` and its cursor's load. -/
theorem l10_atoms_fn :
    let as := topAtoms (fn% «verify_tables_loop0»).body
    as.contains (.mul (.n 6) (.n 0) (.n 0)) = true ∧ as.contains (.mul (.n 7) (.n 6) (.n 0)) = true ∧
      as.contains (.mul (.n 8) (.n 7) (.n 7)) = true ∧ as.contains (.mul (.n 9) (.n 8) (.n 0)) = true ∧
      as.contains (.mul (.n 10) (.n 2) (.n 9)) = true ∧ as.contains (.load (.n 11) (.n 10) 5) = true := by
  decide +kernel

/-- The stream-cursor loops' names. -/
theorem stK_cases {fn : Fn} {D v S : ℕ} (hk : stK fn = some (D, v, S)) :
    (fn.name = name% «keccak_layer__L0_loop0» ∧ D = 17 ∧ v = 20 ∧ S = 16) ∨
    (fn.name = name% «keccak_layer__L1_loop0» ∧ D = 17 ∧ v = 20 ∧ S = 16) ∨
    (fn.name = name% «keccak_layer__L0_loop1» ∧ D = 17 ∧ v = 14 ∧ S = 2) ∨
    (fn.name = name% «keccak_layer__L1_loop1» ∧ D = 17 ∧ v = 14 ∧ S = 2) ∨
    (fn.name = name% «verify_tables_loop0» ∧ D = 22 ∧ v = 11 ∧ S = 3) ∨
    (∃ p < 4, ∃ o < 2, fn.name = B1.Tables.glLoopName p o ∧ D = 10 ∧ v = 17 ∧ S = 32) := by
  have hm := CoreMode.lookup_memL hk
  simp only [CoreMode.stLoops, List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq, List.not_mem_nil,
    or_false] at hm
  rcases hm with (⟨h, rfl, rfl, rfl⟩ | ⟨h, rfl, rfl, rfl⟩ | ⟨h, rfl, rfl, rfl⟩ | ⟨h, rfl, rfl, rfl⟩ |
    ⟨h, rfl, rfl, rfl⟩) | ⟨n, hn, h, rfl, rfl, rfl⟩
  · exact Or.inl ⟨h, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨h, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, rfl, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, rfl, rfl⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by omega, 0, by omega, h.symm, rfl, rfl, rfl⟩, ⟨1, by omega, 0, by omega, h.symm, rfl, rfl, rfl⟩,
      ⟨2, by omega, 0, by omega, h.symm, rfl, rfl, rfl⟩, ⟨3, by omega, 0, by omega, h.symm, rfl, rfl, rfl⟩,
      ⟨0, by omega, 1, by omega, h.symm, rfl, rfl, rfl⟩, ⟨1, by omega, 1, by omega, h.symm, rfl, rfl, rfl⟩,
      ⟨2, by omega, 1, by omega, h.symm, rfl, rfl, rfl⟩, ⟨3, by omega, 1, by omega, h.symm, rfl, rfl, rfl⟩]

/-- **A stream-cursor loop is not of the ghost family `ml`.** -/
theorem stK_mlK {fn : Fn} {p : ℕ × ℕ × ℕ} (hk : stK fn = some p) : CoreMode.mlK fn = none := by
  obtain ⟨D, v, S⟩ := p
  have hmk : ∀ n ∈ CoreMode.stLoops.map (·.1),
      ((List.range 17).find? fun k ↦ B1.Digest.mlNames.getD k "" == n) = none := by decide +kernel
  have hm := List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk)
  unfold CoreMode.mlK
  rw [hmk _ hm]
  rfl

/-- **The keccak layer's loops' cursors** in the stream: `LoopQ` and the iteration's record and load. -/
theorem st_keccak {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {first : ℕ} (hfi : first < 2) (rem : Bool) (hn : f = stLoop first rem) :
    ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + 17 < maxCells ∧
      σ (loopCur rem) = refMem r.img (a + 17) * gen ^ q ∧ q + stStep rem ≤ 8192 := by
  obtain ⟨a, j, n, q, hhd, ha17, -, -, hjn, -, hld, hroom⟩ := loopQ_all hr I hI f σ bufs kids ht first hfi rem hn
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hn] at hf
  obtain ⟨tm, tl⟩ := loop_atoms_top hfi rem hf
  have e6 : σ (.n 6) = σ (.n 2) * σ (.n 0) :=
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp tm))
  have hl : LoadHolds r.img.read (σ (.n 6)) 80 (σ (loopCur rem)) :=
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp tl))
  rw [e6] at hl
  exact ⟨a, q, hhd, ha17, loadHolds_unique hl hld, room_of hjn hroom⟩

/-- **A gkr layer's loop's cursor** in the stream: `GlLQ` and the iteration's load. -/
theorem st_gl {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {p o : ℕ} (hp : p < 4) (ho : o < 2) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node (B1.Tables.glLoopName p o) σ bufs kids) :
    ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + 10 < maxCells ∧
      σ (.n 17) = refMem r.img (a + 10) * gen ^ q ∧ q + 32 ≤ 8192 := by
  obtain ⟨a, k, m, q, hhd, ha10, -, -, hkm, -, hld, hroom⟩ := glLQ_all hr I hI p hp o ho σ bufs kids ht
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain ⟨fn, hf, -, hb⟩ := B1.Tables.glIs_sound (B1.Tables.glIs_loops p hp o ho)
  obtain rfl : fn' = fn := Option.some.inj (hf'.symm.trans hf)
  exact ⟨a, q, hhd, ha10, (gll_next hp ho hb hw hh hld).1, room_of hkm hroom⟩

/-- **`verify_tables`' rounds loop's cursor** in the stream: `VtLQ` and the iteration's record and load. -/
theorem st_vt {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_tables_loop0» σ bufs kids) :
    ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + 22 < maxCells ∧
      σ (.n 11) = refMem r.img (a + 22) * gen ^ q ∧ q + 3 ≤ 8192 := by
  obtain ⟨a, jj, n, q, hhd, ha22, -, -, hjn, -, hld, hroom⟩ := vtLQ_all hr I hI σ bufs kids ht
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn' = fn% «verify_tables_loop0» := Option.some.inj (hf'.symm.trans find_l10)
  obtain ⟨t6, t7, t8, t9, t10, tl⟩ := l10_atoms_fn
  have m6 : σ (.n 6) = σ (.n 0) * σ (.n 0) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t6))
  have m7 : σ (.n 7) = σ (.n 6) * σ (.n 0) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t7))
  have m8 : σ (.n 8) = σ (.n 7) * σ (.n 7) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t8))
  have m9 : σ (.n 9) = σ (.n 8) * σ (.n 0) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t9))
  have m10 : σ (.n 10) = σ (.n 2) * σ (.n 9) := hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp t10))
  have l11 : LoadHolds r.img.read (σ (.n 10)) 5 (σ (.n 11)) :=
    hh _ (topAtoms_on_path hw (List.contains_iff_mem.mp tl))
  have e10 : σ (.n 10) = σ (.n 2) * σ (.n 0) ^ 7 := by rw [m10, m9, m8, m7, m6]; ring
  rw [e10] at l11
  exact ⟨a, q, hhd, ha22, loadHolds_unique l11 hld, room_of hjn hroom⟩

/-- **The stream-cursor family at an honest instance**: its header names its caller's frame `a`, its reads past its
cursor lie in the stream at the caller's cell `D`, its ghost words that stream and the frame's address. -/
theorem st_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {D v S : ℕ} (hk : stK fn = some (D, v, S)) :
    ∃ a, I.hdr.2 = ofK (addressOfIndex a) ∧ a + D < maxCells ∧
      ∀ x, stSub fn x = true → x.Holds (setG σ [refMem r.img (a + D), ofK (Parameters.g ^ a)]) := by
  have hname : fn.name = f := find_name' hf
  have hgb : ∀ v, v < 21 → v < CoreMode.GB := fun v hv ↦ by unfold CoreMode.GB; omega
  rcases stK_cases hk with ⟨hn, rfl, rfl, rfl⟩ | ⟨hn, rfl, rfl, rfl⟩ | ⟨hn, rfl, rfl, rfl⟩ | ⟨hn, rfl, rfl, rfl⟩ |
    ⟨hn, rfl, rfl, rfl⟩ | ⟨p, hp, o, ho, hn, rfl, rfl, rfl⟩
  · obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := st_keccak hr hI ht hf (first := 0) (by decide) false
      (by rw [← hname, hn]; rfl)
    exact ⟨a, hhd, ha, stSub_holds hk (hgb _ (by decide)) hcur hroom⟩
  · obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := st_keccak hr hI ht hf (first := 1) (by decide) false
      (by rw [← hname, hn]; rfl)
    exact ⟨a, hhd, ha, stSub_holds hk (hgb _ (by decide)) hcur hroom⟩
  · obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := st_keccak hr hI ht hf (first := 0) (by decide) true
      (by rw [← hname, hn]; rfl)
    exact ⟨a, hhd, ha, stSub_holds hk (hgb _ (by decide)) hcur hroom⟩
  · obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := st_keccak hr hI ht hf (first := 1) (by decide) true
      (by rw [← hname, hn]; rfl)
    exact ⟨a, hhd, ha, stSub_holds hk (hgb _ (by decide)) hcur hroom⟩
  · rw [← hname, hn] at ht
    obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := st_vt hr hI ht
    exact ⟨a, hhd, ha, stSub_holds hk (hgb _ (by decide)) hcur hroom⟩
  · rw [← hname, hn] at ht
    obtain ⟨a, q, hhd, ha, hcur, hroom⟩ := st_gl hr hI hp ho ht
    exact ⟨a, hhd, ha, stSub_holds hk (hgb _ (by decide)) hcur hroom⟩

/-- **A stream-cursor loop's linked cells** at its frame: the caller's cell `D` its first ghost word, the caller's
frame its second. -/
theorem stGlF {r : Ref} {Cf : CFun} {fp a D : ℕ} {σ : Val} (hgl : Cf.gl = CoreMode.loopGl Cf.fn.params.length [D])
    (hgh : Cf.H.sig.ghosts = 2) (hD : D ≠ 0) (hRd : CoreMode.Rd r.img fp 1 = some (ofK (Parameters.g ^ a)))
    (haD : a + D < maxCells) :
    GlF r.img Cf.gl fp (Cf.fn.params.map (setG σ [refMem r.img (a + D), ofK (Parameters.g ^ a)]) ++
      ownG Cf.H.sig (setG σ [refMem r.img (a + D), ofK (Parameters.g ^ a)])) := by
  rw [ownG_setG (by rw [hgh]; rfl), hgl]
  intro d b k hm
  simp only [CoreMode.loopGl, List.length_singleton, List.range_one, List.map_cons, List.map_nil, List.getD_cons_zero,
    add_zero, List.singleton_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  have hsl : ∀ j, CoreMode.slotW (Cf.fn.params.map (setG σ [refMem r.img (a + D), ofK (Parameters.g ^ a)]) ++
      [refMem r.img (a + D), ofK (Parameters.g ^ a)]) (Cf.fn.params.length + j) =
      [refMem r.img (a + D), ofK (Parameters.g ^ a)].getD j 0 := fun j ↦ by
    simp [CoreMode.slotW, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨a, hRd, haD, ?_⟩
    simp only [CoreMode.LinkW, hD, ↓reduceIte]
    rw [show Cf.fn.params.length = Cf.fn.params.length + 0 from rfl, hsl 0]
    simp
  · refine ⟨a, hRd, by omega, ?_⟩
    simp only [CoreMode.LinkW, ↓reduceIte]
    rw [hsl 1]
    simp

end

end LeanVM.Guest.EndExec
