/-
  LeanVM.Guest.EndExecCoreSt

  The core route's stream-cursor family at the honest instances: a loop's reads past its cursor lie in its
  caller's proof stream.
-/

module

public import LeanVM.Guest.EndExecCoreLink

/-!
# The stream-cursor family, sound

At an honest instance of a stream-cursor loop (`stK`, each its function's own, `FnReg.stLoops`) its header names its
caller's frame `a`, whose cell `D` holds the proof stream, and the cursor the body loads from its record is
`M (a + D)·g^q` with room for an iteration's words (`EndExec.StOk`, proved by the loop's function); with its ghost words
that stream and the frame's address (`setG σ [M (a + D), g^a]`), each read of the family (`stSub`) lies in the stream,
`q + c < 8192` (`stSub_holds`; `st_inst`, `EndExecCoreResAll`). `stGlF`: its linked cells hold. `stK_mlK`, `cmK_mlK`,
`cmK_stK`: the ghost families' functions are distinct, by their registries.
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
    simp only [addressOfIndex, pow_add, pow_zero, LeanVM.Parameters.ofK_mul]
    rw [LeanVM.Parameters.ofK_one]
    ring_nf
  | .lt _ _, hx | .nz _, hx | .subR _ _, hx | .under _ _, hx | .subP _ _, hx => simp [stSub] at hx

theorem room_of {q S n j : ℕ} (hjn : j < n) (h : q + S * (n - j) ≤ 8192) : q + S ≤ 8192 := by
  have : S ≤ S * (n - j) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **A stream-cursor loop is not of the ghost family `ml`.** -/
theorem stK_mlK {fn : Fn} {p : ℕ × ℕ × ℕ} (hk : stK fn = some p) : CoreMode.mlK fn = none := by
  obtain ⟨D, v, S⟩ := p
  have hmk : ∀ n ∈ CoreMode.stLoops.map (·.1),
      CoreMode.FnReg.mlLoops.lookup n = none := by decide +kernel
  exact hmk _ (List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk))

/-- **A frame loop is not of the families `ml`, `st`.** -/
theorem cmK_mlK {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × List ℕ} (hk : CoreMode.cmK fn = some p) : CoreMode.mlK fn = none := by
  have hm : ∀ n ∈ CoreMode.FnReg.cmLoops.map (·.1), CoreMode.FnReg.mlLoops.lookup n = none := by decide +kernel
  exact hm _ (List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk))

theorem cmK_stK {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × List ℕ} (hk : CoreMode.cmK fn = some p) : CoreMode.stK fn = none := by
  have hm : ∀ n ∈ CoreMode.FnReg.cmLoops.map (·.1), CoreMode.stLoops.lookup n = none := by decide +kernel
  exact hm _ (List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk))

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
