/-
  LeanVM.Guest.B1.VerifySub.CPlaced5

  `verify_sub` placed: the honest valuation's path, its events holding of the honest calls, and
  the calls' words read off them.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced4

/-!
# `verify_sub`'s path and calls

`vs_run`: over the honest memory, a valuation fixing the run's values walks the body through the
dispatch at some `sel < 28`, every event holding of `vsC` (the honest calls). `vs_calls`: the
frames of that path, and each entered one's words among the honest calls.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig

@[expose] public section

set_option maxRecDepth 100000 in
theorem vsPre1_noRet : Core.Stmt.noRetList vsPre1 = true := by decide +kernel

variable {rd : Reader} {D : VsData} {P : VsPtrs} {out lp sq : E} {bytecode : List K}

set_option maxRecDepth 100000 in
/-- **The honest path**: a valuation taking the run's values, its parameters the arguments,
walks the body through `open_stacked__L{sel}`, every event holding of the honest calls. -/
theorem vs_run (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode)
    (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out) :
    ∃ (σ : Val) (sel : ℕ), sel < 28 ∧ Fixes σ (vsG11 D P lp sq out) ∧
      (Fn.params Data.core15).map σ = [(digestScalars D.pi).1, (digestScalars D.pi).2,
        (digestScalars D.seed).1, (digestScalars D.seed).2, lp, sq, out] ∧
      walk σ (Fn.body Data.core15) = .ret (vsEvs σ sel) [] ∧
      ∀ e ∈ vsEvs σ sel, e.Ok (vsC bytecode D P lp sq) rd σ := by
  set σ0 := upds (fun _ => 0) (vsG0 D lp sq out)
  have h0 : Fixes σ0 (vsG0 D lp sq out) := by
    intro p hp; simp only [vsG0, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [σ0, vsG0, upds_n]
  obtain ⟨σ, he, hfix, hh⟩ := vs_body (C := vsC bytecode D P lp sq) hlow hb hok ht hm vsCallsOk_mem σ0 h0
  have hH : Stmt.HoldsList (vsC bytecode D P lp sq) rd σ (vsBody ++ [.ret []]) True
      (fun r => r = []) := by
    rw [holdsList_append]; exact hh _ _ rfl
  have hd := hH
  rw [vsBody_split, List.append_assoc, List.cons_append, holdsList_append,
    holdsList_noRet _ vsPre1_noRet] at hd
  obtain ⟨-, hd⟩ := hd
  simp only [Stmt.HoldsList, vsDisp, Stmt.Holds] at hd
  obtain ⟨⟨sel, hsel, hx, -⟩, -⟩ := hd
  have hsel' : sel < 28 := by simpa [openNames] using hsel
  have hw := vs_walk σ hsel' hx
  have hwf : Stmt.wfList coreProgram (vsBody ++ [.ret []]) = true := by
    have := coreProgram_wf Data.core15 (List.mem_of_find?_eq_some find_verify_sub)
    rwa [core15_body'] at this
  have hs := walk_sat _ hwf hH
  rw [hw] at hs
  refine ⟨σ, sel, hsel', hfix, ?_, by rw [core15_body']; exact hw, hs.1⟩
  have hp : ∀ k < 7, σ (.n k) = σ0 (.n k) := fun k hk => he.apply (Or.inl hk)
  simp only [core15_params, List.map_cons, List.map_nil, hp 0 (by omega), hp 1 (by omega),
    hp 2 (by omega), hp 3 (by omega), hp 4 (by omega), hp 5 (by omega), hp 6 (by omega)]
  simp [σ0, vsG0, upds_n]

/-- **The path's frames**, the entered ones holding of the honest calls. -/
theorem vs_calls {σ : Val} {sel : ℕ} (h : ∀ e ∈ vsEvs σ sel, e.Ok (vsC bytecode D P lp sq) rd σ) :
    calls (vsEvs σ sel) = (vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
      [⟨openNames.getD sel "", [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726],
        [.n 1648, .n 1649, .n 1650, .n 1651], true⟩,
        ⟨"check_opening_terminal", [.n 418, .n 709, .n 715, .n 417, .n 713, .n 144, .n 718, .n 8,
          .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651, .n 1648], [],
          true⟩] ∧
      ∀ c ∈ calls (vsEvs σ sel), c.taken = true →
        (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriples bytecode D P lp sq := by
  refine ⟨?_, calls_ok h⟩
  rw [(vs_parts σ sel).2.2.2.1, vsPost2_calls]
  simp [Main.mkCall]

end
end LeanVM.Guest.B1.VerifySub
