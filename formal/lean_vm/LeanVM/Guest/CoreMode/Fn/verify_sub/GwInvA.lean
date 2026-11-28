/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.GwInvA

  `verify_sub`'s residual over the windows-table index `g_w·g^-1` (`gwInvFam`), sound at its honest instances: the
  index's word is `g_log_mem·[460]·g^-1 = g_w·g^-1 = g^(w - 1)`, `w ≤ 24`.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_sub.GwInv
public import LeanVM.Guest.CoreMode.Fn.verify_sub.ChalA
public import LeanVM.Guest.B1.VerifySub.PhLinkShape
public import LeanVM.Guest.B1.VerifySub.Reads

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Guest.CoreMode
open LeanVM.Protocol.Verifier (gen)

public section

/-- **The index's equations** in `verify_sub`'s body: `g_log_mem = [108]·g` (`vsReadsT`), `g_w = [460]·g_log_mem`
(`vsShapeAT`'s `assert log(g_w / g_log_mem) < 24`), and on the `flag == 1` arm `[472] = g^-1` (`vsShapeIteT`). -/
theorem vs_gwInv_eqs {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (hpre : Stmt.HoldsList C rd σ B1.VerifySub.vsPre True kret) :
    σ (.n 101) = σ (.n 108) * gen ∧ σ (.n 409) = σ (.n 460) * σ (.n 101) ∧
      (σ (.n 471) = 0 → σ (.n 472) = B1.Digest.ginvW) := by
  refine ⟨(B1.VerifySub.readsFacts (vs_slice hpre B1.VerifySub.vsReadsT_eq)).memMul, ?_, ?_⟩
  · have hA := vs_slice hpre B1.VerifySub.vsShapeAT_eq
    simp only [B1.VerifySub.vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, s40, -⟩ := hA
    exact s40
  · intro h471
    have hI := vs_slice hpre B1.VerifySub.vsShapeIteT_eq
    simp only [B1.VerifySub.vsShapeIteT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hI
    obtain ⟨-, hz1, -⟩ := hI
    exact (hz1 h471).1

/-- **`gwInvFam` holds** where `g_w = g^(e + 19)`, `e ≤ 5`, and the index's equations do. -/
theorem gwInvFam_holds {σ : Val} {e : ℕ} (he : e ≤ 5) (h409 : σ (.n 409) = gen ^ (e + 19))
    (H : σ (.n 101) = σ (.n 108) * gen ∧ σ (.n 409) = σ (.n 460) * σ (.n 101) ∧
      (σ (.n 471) = 0 → σ (.n 472) = B1.Digest.ginvW)) {x : CRes} (hx : gwInvFam x = true) : x.Holds σ := by
  obtain ⟨h101, hsplit, h472⟩ := H
  unfold gwInvFam at hx
  split at hx
  · rename_i g c m
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, Nat.blt_eq] at hx
    obtain ⟨⟨⟨hg, rfl⟩, h24⟩, hcap⟩ := hx
    simp only [CRes.Holds]
    intro hc
    have h0 : σ (.n 471) = 0 := hc _ (List.contains_iff_mem.mp hg)
    have hw : gwInvC.valW (vw σ) = gen ^ (e + 18) := by
      rw [show gwInvC = ⟨[(108, 1), (460, 1), (472, 1)], 1⟩ from rfl, valW_gen]
      simp only [prodW, vw, pow_one, mul_one]
      rw [h472 h0, show e + 18 = e + 19 - 1 by omega, ← B1.VerifySub.pow_mul_ginv (w := e + 19) (by omega), ← h409,
        hsplit, h101]
      ring
    refine ⟨e + 18, m, ?_, rep_const hcap, by omega⟩
    show rep (gwInvC.valW (vw σ)) = some (e + 18)
    rw [hw, Value.gen_pow_eq_ofK]
    exact rep_of (by unfold capE; omega)
  · cases hx

end

end LeanVM.Guest.CoreMode.Own.verify_sub
