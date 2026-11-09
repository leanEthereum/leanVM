/-
  LeanVM.Guest.B1.Ring.TargetComplete

  `ring_switch_target` is complete in the uniform placed form (`CompleteAtD`): its chain at the
  bump allocator's position, its loop loading the slices, the challenges and the chain.
-/

module

public import LeanVM.Guest.B1.Ring.Loop14Complete
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.Memory.LiftPure

/-!
# `ring_switch_target`, placed (TRIAGE G #64, #65)

On the caller's words — the 64 slices `s` at `g^bs`, the six challenges `chs` at `g^bm` —
`ring_switch_target` is complete at every frame pointer `fp` (`rst_completeAt`): its chain
(`HeapBuf` of 18 words) at `fp + fs "ring_switch_target"` holds the honest rows `chainWords s chs`,
its `__loop13` (pure) is complete by `l14_relIn` lifted by `Lift.completeAtD_of_relIn`, and it
returns `Σ_i g^i Φ(s_i)` (`runL_eight`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The chain's last sum -/

theorem take_drop_getD (s : List E) (n i : ℕ) (hi : i < 8) :
    ((s.drop n).take 8).getD i 0 = s.getD (n + i) 0 := by
  simp [List.getD_eq_getElem?_getD, hi, List.getElem?_drop]

theorem runL_sum (s chs : List E) : ∀ j,
    runL s chs j = ∑ k ∈ Finset.range (8 * j), gen ^ k * phiMap (s.getD k 0) chs
  | 0 => by simp [runL]
  | j + 1 => by
    rw [runL, runL_sum s chs j, show 8 * (j + 1) = 8 * j + 8 by ring, Finset.sum_range_add,
      chunkOf, rsChunk, Finset.mul_sum]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => ?_)
    rw [take_drop_getD s _ i (Finset.mem_range.1 hi), pow_add]
    ring

theorem runL_eight {s chs : List E} (hs : s.length = 64) :
    runL s chs 8 = polyEval (s.map (phiMap · chs)) gen := by
  rw [runL_sum, polyEval_eq_sum, List.length_map, hs]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 64 := Finset.mem_range.1 hk
  rw [List.getD_eq_getElem (s.map _) _ (by simpa [hs] using hk'), List.getElem_map,
    List.getD_eq_getElem s _ (by omega)]
  ring

/-! ## The body -/

/-- `ring_switch_target`'s statements before its `ret`. -/
def rstPre : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 18)), .atom (.const (.n 3) (word 1 0 0)),
    .atom (.load (.n 3) (.n 2) 0), .atom (.const (.n 4) (word 0 0 0)),
    .atom (.load (.n 4) (.n 2) 1), .atom (.const (.n 5) (word 1 0 0)),
    .call "__loop13" [.n 5, .n 0, .n 1, .n 2] [], .atom (.const (.n 6) (word 65536 0 0)),
    .atom (.mul (.n 7) (.n 2) (.n 6)), .atom (.load (.n 8) (.n 7) 1)]

theorem rst_body' : Fn.body Data.core13 = rstPre ++ [.ret [.n 8]] := by
  rw [show Fn.body Data.core13 = rstT from rst_body]; rfl

theorem rst_flat : rstPre.all Stmt.flat = true := by decide +kernel

theorem rst_addrs : rstPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rst_allocs : rstPre.filterMap Main.Stmt.allocSz = [(.n 2, .inl 18)] := by decide +kernel

theorem rst_loads : rstPre.filterMap Stmt.loadS = [(.n 2, 0), (.n 2, 1), (.n 7, 1)] := by
  decide +kernel

theorem rst_not_loop : coreProgram.loop "ring_switch_target" = false := by decide +kernel

theorem l14_pure : coreProgram.PureIn ["__loop13"] := by
  intro g hg fn hf
  rw [List.mem_singleton] at hg
  subst hg
  rw [find_loop14, Option.some.injEq] at hf
  subst hf
  decide +kernel

/-- The honest valuation of `ring_switch_target`'s body. -/
noncomputable def rstσ (sl mc buf r : E) : Val :=
  B1.Val.ofArgs [sl, mc, buf, word 1 0 0, word 0 0 0, word 1 0 0, word 65536 0 0,
    buf * word 65536 0 0, r]

theorem rst_callSF (σ : Val) : rstPre.filterMap (Stmt.callSF σ) =
    [(none, "__loop13", [.n 5, .n 0, .n 1, .n 2], [])] := rfl

/-- The chain's words read through `g^b`. -/
theorem chain_load {rd : Reader} {s chs : List E} {b : ℕ}
    (h : ReadsAt rd (ofK (Parameters.addressOfIndex b)) (chainWords s chs)) {k : ℕ} (hk : k < 18) :
    LoadHolds rd (ofK (Parameters.addressOfIndex b)) k
      (if k % 2 = 0 then gen ^ (8 * (k / 2)) else runL s chs (k / 2)) := by
  have := h k (by rw [chainWords_length]; exact hk)
  rwa [chainWords_get] at this

/-- The regions of `__loop13`'s caller's words. -/
def l14Lin (bs bm bc : ℕ) (s chs : List E) : Main.Layout := [(bs, s), (bm, chs), (bc, chainWords s chs)]

theorem l14_relIn_lin {rd : Reader} {bs bm bc : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 6) (hL : MemL rd (l14Lin bs bm bc s chs)) :
    coreProgram.RelIn rd (RegionL (l14Lin bs bm bc s chs)) "__loop13"
      [1, ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm), ofK
          (Parameters.addressOfIndex bc)] [] := by
  have := l14_relIn hs hc (hL (bs, s) (by simp [l14Lin])) (hL (bm, chs) (by simp [l14Lin]))
    (hL (bc, chainWords s chs) (by simp [l14Lin])) (R := RegionL (l14Lin bs bm bc s chs)) (fun i hi => by
      rcases hi with hi | hi | hi
      · exact ⟨(bs, s), by simp [l14Lin], by simpa [hs] using hi⟩
      · exact ⟨(bm, chs), by simp [l14Lin], by simpa [hc] using hi⟩
      · exact ⟨(bc, chainWords s chs), by simp [l14Lin], by simpa [chainWords_length] using hi⟩)
    7 0 rfl
  rwa [pow_zero] at this

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`ring_switch_target` is complete, placed**: on the slices and the challenges, at every frame
pointer, its chain at the bump allocator's position, returning `Σ_i g^i Φ(s_i)`. -/
theorem rst_completeAt (κ : ℕ) {bs bm : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 6) :
    CompleteAtD fs cert κ "ring_switch_target" [(bs, s), (bm, chs)]
      [ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm)]
      (Returns [polyEval (s.map (phiMap · chs)) gen]) := by
  refine completeAt_flatD (fs := fs) (cert := cert) find_rst rst_not_loop κ _ _ _ rst_body' rst_flat
    rst_addrs [18] (fun _ ↦ [chainWords s chs]) (fun _ ↦ by simp [chainWords_length])
    (fun fp ↦ [⟨"__loop13", true, [1, ofK (Parameters.addressOfIndex bs), ofK
        (Parameters.addressOfIndex bm),
      ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))], l14Lin bs bm (fp + fs "ring_switch_target") s chs, Returns []⟩])
    ?_ ?_ ?_ ?_
  · -- the loop, placed
    intro fp k hk _
    rw [List.mem_singleton] at hk
    subst hk
    exact Lift.completeAtD_of_relIn l14_pure (List.mem_singleton_self _)
      fun rd _ hL ↦ l14_relIn_lin hs hc hL
  · -- the loop's words: the caller's and the chain
    intro fp k hk _ i hi
    rw [List.mem_singleton] at hk
    subst hk
    obtain ⟨q, hq, hi⟩ := hi
    simp only [l14Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
  · intro fp rd hB hLin k hk
    rw [List.mem_singleton] at hk
    subst hk
    intro q hq
    simp only [l14Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hLin (bs, s) (by simp)
    · exact hLin (bm, chs) (by simp)
    · exact hB (fp + fs "ring_switch_target", chainWords s chs) (by simp [bufL, bases])
  · -- the honest valuation
    intro fp outs ho rd _ hB hLin
    have hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s := hLin (bs, s) (by simp)
    have hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs := hLin (bm, chs) (by simp)
    have hch : ReadsAt rd (ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))) (chainWords s chs) :=
      hB (fp + fs "ring_switch_target", chainWords s chs) (by simp [bufL, bases])
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact absurd ho (by simp [OutsOk])
    swap
    · exact absurd ho.2 (by simp [OutsOk])
    obtain ⟨ho', -⟩ := ho
    obtain ⟨ho1, -⟩ := ho' rfl
    have hw16 : word 65536 0 0 = gen ^ 16 := by
      rw [show (65536 : ℕ) = 2 ^ 16 from rfl]; exact word_two_pow (by decide)
    refine ⟨rstσ (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bm))
      (ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))) (polyEval (s.map (phiMap · chs)) gen), rfl, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro st hst
      simp only [rstPre, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    · rw [rst_body']
      refine Fwd.holdsList_straight _ _ _ _ (fun st hst ↦ ?_) rfl
      simp only [rstPre, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · rfl
      · show LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))) 0
          (word 1 0 0)
        have := chain_load hch (k := 0) (by norm_num)
        simpa [word_one] using this
      · rfl
      · show LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))) 1
          (word 0 0 0)
        have := chain_load hch (k := 1) (by norm_num)
        simpa [word_zero, runL] using this
      · rfl
      · show coreProgram.Rel rd "__loop13" [word 1 0 0, ofK (Parameters.addressOfIndex bs),
          ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex (fp + fs
              "ring_switch_target"))] []
        rw [word_one]
        exact (l14_relIn_lin hs hc (fun q hq ↦ by
          simp only [l14Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact hsl
          · exact hmc
          · exact hch)).rel
      · rfl
      · rfl
      · show LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target")) * word
          65536 0 0) 1
          (polyEval (s.map (phiMap · chs)) gen)
        rw [hw16, loadHolds_mul_gen_pow, ← runL_eight hs]
        have := chain_load hch (k := 17) (by norm_num)
        simpa using this
    · rw [rst_allocs]; rfl
    · rw [rst_allocs]; rfl
    · rw [rst_callSF]
      refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
      · change [word 1 0 0, ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm),
          ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))] = _
        rw [word_one]
      · change [] = o.1
        rw [ho1]
    · intro q hq
      replace hq := filterMap_of_loadsEv (by decide +kernel) hq
      rw [rst_loads] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨fp + fs "ring_switch_target" + 0, Main.addr_ofK _ _, Or.inr
          ⟨(fp + fs "ring_switch_target", chainWords s chs), by simp [bufL, bases],
            by simp [chainWords_length]⟩⟩
      · exact ⟨fp + fs "ring_switch_target" + 1, Main.addr_ofK _ _, Or.inr
          ⟨(fp + fs "ring_switch_target", chainWords s chs), by simp [bufL, bases],
            by simp [chainWords_length]⟩⟩
      · refine ⟨fp + fs "ring_switch_target" + 16 + 1, ?_, Or.inr
          ⟨(fp + fs "ring_switch_target", chainWords s chs), by simp [bufL, bases],
            by simp only [chainWords_length]; omega⟩⟩
        show (ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target")) * word 65536 0 0).limb 0 * Parameters.addressOfIndex 1 = _
        rw [hw16, rt_addr_mul]

end
end LeanVM.Guest.B1.VerifySub
