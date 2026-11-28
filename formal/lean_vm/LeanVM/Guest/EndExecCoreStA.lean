/-
  LeanVM.Guest.EndExecCoreStA

  The core route's cursor-run family (`CoreMode.stK`) at the honest instances of b2c's aligned tree: the bus era's
  stream-cursor family `EndExecCoreSt` on `instsR`, its run past a caller's cell generalized to `W` residues below the
  exponent of another.
-/

module

public import LeanVM.Guest.EndExecCoreLinkA

/-!
# The cursor-run family, aligned

A cursor-run loop (`stK fn = some (Db, Dn, W, v, S)`, each its function's own, `FnReg.stLoops`) reads `[v]·g^c`, `c < S`,
past the cursor `v` its body loads from its record (`stSub`), and links its first two ghost slots to its caller's cells
`Db`, `Dn`, its third to its caller's frame (`stGl`). `StLoopOkA al D c`, what its function's soundness owes: at every
honest instance of `instsR`, its header names its caller's frame `a`, whose cell `Dn` holds `g^n`, and its cursor is
`M·g^(W·m)`, `M` the word at the caller's cell `Db`, with `W·m + S ≤ W·n`. At the ghost words `[M, g^n, g^a]` its reads
lie in the residue runs `[ghost₀]·g^d·[0, e(ghost₁))` of stride `W` (`stSub_holds`) and its linked cells hold (`stGlF`);
`st_instA`. `stK_mlK`, `cmK_stK`: the ghost families' functions are distinct, by their registries.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes stK stSub GlF setG setG_eq ownG ownG_setG prodW vw capE rep_of rep_const)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- **A cursor-run loop's cursor** at every honest instance, aligned: its header names its caller's frame `a`, `Db` and
`Dn` nonzero, the cursor `v < GB`, `S > 0`; the caller's cell `Dn` holds `g^n`, the cursor is the word at its cell `Db`
times `g^(W·m)`, room for `S` words before `W·n`. -/
def StLoopOkA (al : String → Bool) (D : Ref → RefD) (c : String × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  c.2.1 ≠ 0 ∧ c.2.2.1 ≠ 0 ∧ c.2.2.2.2.1 < CoreMode.GB ∧ 0 < c.2.2.2.2.2 ∧
    ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ I ∈ instsR al D r, ∀ σ bufs kids,
      I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn →
        ∃ a m n, I.hdr.2 = ofK (addressOfIndex a) ∧ a + c.2.1 < maxCells ∧ a + c.2.2.1 < maxCells ∧
        σ (.n c.2.2.2.2.1) = refMem r.img (a + c.2.1) * gen ^ (c.2.2.2.1 * m) ∧
        refMem r.img (a + c.2.2.1) = gen ^ n ∧ n < capE ∧ c.2.2.2.1 * m + c.2.2.2.2.2 ≤ c.2.2.2.1 * n

end

public section

theorem setG_ghosts3 (σ : Val) (u w z : E) :
    setG σ [u, w, z] (V.n CoreMode.GB) = u ∧ setG σ [u, w, z] (V.n (CoreMode.GB + 1)) = w := by
  have h := ownG_setG (G := ({ ghosts := 3 } : CoreMode.HSig)) (σ := σ) (gw := [u, w, z]) rfl
  have h0 := congrArg (·[0]?) h
  have h1 := congrArg (·[1]?) h
  simp only [CoreMode.ownG, List.getElem?_map, List.getElem?_range (show 0 < 3 by decide), Option.map_some,
    List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at h0
  simp only [CoreMode.ownG, List.getElem?_map, List.getElem?_range (show 1 < 3 by decide), Option.map_some,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1
  exact ⟨h0, h1⟩

/-- **A read past a cursor holds** at the valuation whose first ghosts are the run's base `M` and `g^n`, the cursor
`σ v = M·g^(W·m)` with room for `S` words before `W·n`. -/
theorem stSub_holds {fn : Fn} {Db Dn W v S : ℕ} (hk : stK fn = some (Db, Dn, W, v, S)) (hv : v < CoreMode.GB)
    (hS : 0 < S) {σ : Val} {M z : E} {m n : ℕ} (hcur : σ (.n v) = M * gen ^ (W * m)) (hn : n < capE)
    (hroom : W * m + S ≤ W * n) : ∀ x, stSub fn x = true → x.Holds (setG σ [M, gen ^ n, z]) := by
  have hwg : vw (setG σ [M, gen ^ n, z]) CoreMode.GB = M := (setG_ghosts3 σ M _ z).1
  have hwn : vw (setG σ [M, gen ^ n, z]) (CoreMode.GB + 1) = gen ^ n := (setG_ghosts3 σ M _ z).2
  have hrn : CoreMode.rep ((CoreMode.idxC (.val (CoreMode.GB + 1))).valW (vw (setG σ [M, gen ^ n, z]))) = some n := by
    have e : (CoreMode.idxC (.val (CoreMode.GB + 1))).valW (vw (setG σ [M, gen ^ n, z])) =
        ofK (addressOfIndex n) := by
      simp only [CoreMode.idxC, CoreMode.baseC, CoreMode.CCell.valW, prodW, pow_one, mul_one, hwn,
        ← Value.gen_pow_eq_ofK, pow_zero, CoreMode.ofK_oneL]
    rw [e]
    exact rep_of hn
  intro x hx
  match x, hx with
  | .sub c qr, hx =>
    simp only [stSub, hk, Option.any_some, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hx
    obtain ⟨⟨hcb, hc⟩, rfl⟩ := hx
    have hW : 0 < W := by
      rcases Nat.eq_zero_or_pos W with rfl | h
      · simp at hroom; omega
      · exact h
    have hj : m + c.off / W < n := by
      have h1 : W * (c.off / W) ≤ c.off := Nat.mul_div_le c.off W
      have h2 : W * (m + c.off / W) < W * n := by rw [Nat.mul_add]; omega
      exact Nat.lt_of_mul_lt_mul_left h2
    show CoreMode.RunSet _ _ _ _ _ _
    refine ⟨0, n, m + c.off / W, rep_const (by unfold capE; omega), hrn, Nat.zero_le _, hj, ?_⟩
    have hwv : vw (setG σ [M, gen ^ n, z]) v = σ (.n v) := setG_eq (show (V.n v).idx < CoreMode.GB from hv)
    have e : W * m + c.off = c.off % W + W * (m + c.off / W) := by
      have := Nat.mod_add_div c.off W
      rw [Nat.mul_add]
      omega
    have key : σ (.n v) * ofK (addressOfIndex c.off) =
        M * ofK (addressOfIndex (c.off % W)) * ofK (addressOfIndex (W * (m + c.off / W))) := by
      rw [hcur, ← Value.gen_pow_eq_ofK, ← Value.gen_pow_eq_ofK, ← Value.gen_pow_eq_ofK, mul_assoc, mul_assoc,
        ← pow_add, ← pow_add, e]
    unfold CoreMode.CCell.addrW CoreMode.CCell.valW
    rw [hcb]
    simp only [prodW, pow_one, mul_one, hwg, hwv]
    rw [key]
  | .lt a b, hx =>
    simp only [stSub, hk, Option.isSome_some, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨0, n, rep_const (by unfold capE; omega), hrn, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hroom; omega
    · exact h
  | .nz _, hx | .subR _ _, hx | .under _ _, hx | .subP _ _, hx | .eq _ _, hx => simp [stSub] at hx

/-- **A cursor-run loop is not of the ghost family `ml`.** -/
theorem stK_mlK {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × ℕ} (hk : stK fn = some p) : CoreMode.mlK fn = none := by
  have hmk : ∀ n ∈ CoreMode.stLoops.map (·.1), CoreMode.FnReg.mlLoops.lookup n = none := by decide +kernel
  exact hmk _ (List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk))

/-- **A frame loop is not a cursor-run loop.** -/
theorem cmK_stK {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × List ℕ} (hk : CoreMode.cmK fn = some p) : CoreMode.stK fn = none := by
  have hm : ∀ n ∈ CoreMode.FnReg.cmLoops.map (·.1), CoreMode.stLoops.lookup n = none := by decide +kernel
  exact hm _ (List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk))

/-- **A cursor-run loop's linked cells** at its frame: the caller's cells `Db`, `Dn` its first two ghost words, the
caller's frame its third. -/
theorem stGlF {r : Ref} {Cf : CFun} {fp a Db Dn : ℕ} {σ : Val}
    (hgl : Cf.gl = CoreMode.loopGl Cf.fn.params.length [Db, Dn]) (hgh : Cf.H.sig.ghosts = 3) (hDb : Db ≠ 0)
    (hDn : Dn ≠ 0) (hRd : CoreMode.Rd r.img fp 1 = some (ofK (Parameters.g ^ a))) (haDb : a + Db < maxCells)
    (haDn : a + Dn < maxCells) :
    GlF r.img Cf.gl fp (Cf.fn.params.map (setG σ [refMem r.img (a + Db), refMem r.img (a + Dn),
      ofK (Parameters.g ^ a)]) ++ ownG Cf.H.sig (setG σ [refMem r.img (a + Db), refMem r.img (a + Dn),
      ofK (Parameters.g ^ a)])) := by
  rw [ownG_setG (by rw [hgh]; rfl), hgl]
  intro d b k hm
  simp only [CoreMode.loopGl, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton,
    Prod.mk.injEq] at hm
  set gs := [refMem r.img (a + Db), refMem r.img (a + Dn), ofK (Parameters.g ^ a)]
  have hsl : ∀ j, CoreMode.slotW (Cf.fn.params.map (setG σ gs) ++ gs) (Cf.fn.params.length + j) = gs.getD j 0 :=
    fun j ↦ by simp [CoreMode.slotW, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rcases hm with ⟨j, hj, hjd⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hjd
    have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
    rcases hj' with rfl | rfl
    · refine ⟨a, hRd, by simpa using haDb, ?_⟩
      simp only [CoreMode.LinkW, List.getD_cons_zero, hDb, ↓reduceIte]
      rw [hsl 0]
      simp [gs]
    · refine ⟨a, hRd, by simpa using haDn, ?_⟩
      simp only [CoreMode.LinkW, List.getD_cons_succ, List.getD_cons_zero, hDn, ↓reduceIte]
      rw [hsl 1]
      simp [gs]
  · refine ⟨a, hRd, by omega, ?_⟩
    simp only [CoreMode.LinkW, ↓reduceIte, List.length_cons, List.length_nil]
    rw [hsl 2]
    simp [gs]

variable {al : String → Bool} {D : Ref → RefD}

/-- **The cursor-run family at an honest instance**, aligned: its header names its caller's frame `a`, its reads past
its cursor lie in the run at the caller's cells `Db`, `Dn`, its ghost words that run's base, its bound and the frame's
address. -/
theorem st_instA (hst : ∀ c ∈ CoreMode.FnReg.stLoops, StLoopOkA al D c) {r : Ref} (hR : RefH (layB al) (D r) r)
    (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {fn : Fn} (hf : coreProgram.find? f = some fn) {Db Dn W v S : ℕ}
    (hk : stK fn = some (Db, Dn, W, v, S)) :
    Db ≠ 0 ∧ Dn ≠ 0 ∧ ∃ a, I.hdr.2 = ofK (addressOfIndex a) ∧ a + Db < maxCells ∧ a + Dn < maxCells ∧
      ∀ x, stSub fn x = true → x.Holds (setG σ [refMem r.img (a + Db), refMem r.img (a + Dn),
        ofK (Parameters.g ^ a)]) := by
  have hname : fn.name = f := find_name' hf
  obtain ⟨hDb, hDn, hv, hS, hok⟩ := hst _ (CoreMode.lookup_memL hk)
  rw [hname] at hok
  obtain ⟨a, m, n, hhd, ha1, ha2, hcur, hn, hnc, hroom⟩ := hok hR hr I hI σ bufs kids ht fn hf
  refine ⟨hDb, hDn, a, hhd, ha1, ha2, ?_⟩
  rw [hn]
  exact stSub_holds hk hv hS hcur hnc hroom

end

end LeanVM.Guest.EndExec
