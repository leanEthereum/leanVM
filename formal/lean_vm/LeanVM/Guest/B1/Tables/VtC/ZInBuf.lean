/-
  LeanVM.Guest.B1.Tables.VtC.ZInBuf

  Where `verify_tables`' statements `2591 ..< 2690` and `5530 ..< 5564` load: the rounds'
  records, the running products, `claim_pool`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZTail
public import LeanVM.Guest.B1.Tables.VtC.InBuf

/-!
# The loads, inside buffers

`vtZ_inBuf`: the loads of `2591 ..< 2690` read the records (`7(n + 1)` words at `w 2628`, the
last one `7n` on) and the running products (`n + 1` at `w 2631`).
`vtZt_inBuf`: those of `5530 ..< 5564` read `claim_pool` (`159` words).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The loads of `2591 ..< 2690`** read the records and the running products. -/
theorem vtZ_inBuf {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 21) {n : ℕ}
    (hwn : w 2545 = gen ^ n) {bufs : List (E × ℕ)}
    (bR : (w 2628, 7 * (n + 1)) ∈ bufs) (bC : (w 2631, n + 1) ∈ bufs) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop 2591).take 99) := by
  have g0 := vt_goodL (rd := rd) (w := w) hl 2591
    [.atom (.hint (.witness "zc_tau_max" (.stack [.n 2545])))] (by decide +kernel)
  have g1 := vt_goodL (rd := rd) (w := w) hl 2649 [.atom (.hint (.allocDyn (.n 2628) (.n 2627)))]
    (by decide +kernel)
  have g2 := vt_goodL (rd := rd) (w := w) hl 2652 [.atom (.hint (.allocDyn (.n 2631) (.n 2630)))]
    (by decide +kernel)
  have g3 := vt_goodL (rd := rd) (w := w) hl 2673 [.atom (.mul (.n 2642) (.n 2545) (.n 2545)),
    .atom (.mul (.n 2643) (.n 2642) (.n 2545)), .atom (.mul (.n 2644) (.n 2643) (.n 2643)),
    .atom (.mul (.n 2645) (.n 2644) (.n 2545)), .atom (.mul (.n 2646) (.n 2628) (.n 2645))]
    (by decide +kernel)
  have e := tbStmtsEqb_sound zBlk_at
  have hlen : zBlk.length = 99 := rfl
  rw [← hlen, ← e]
  generalize vtσ rd w args = σ at *
  simp only [GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    ↓reduceIte] at g0 g1 g2 g3
  obtain ⟨m22, m23, m24, m25, m26⟩ := g3
  have v2589 : σ (.n 2628) = w 2628 := g1
  have v2603 : σ (.n 2646) = w 2628 * gen ^ (7 * n) := by
    rw [m26, m25, m24, m23, m22, g0.1, hwn, v2589]; ring
  intro d p off hm
  simp only [zBlk, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, false_or,
    or_false, List.not_mem_nil] at hm
  have hR : ∀ k < 7, InBuf σ bufs (.n 2628) k := fun k hk => ⟨_, bR, 0, by rw [v2589]; simp,
    by omega⟩
  have hN : ∀ k < 7, InBuf σ bufs (.n 2646) k := fun k hk => ⟨_, bR, 7 * n, v2603, by omega⟩
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals first
    | exact hR _ (by norm_num)
    | exact hN _ (by norm_num)
    | exact ⟨_, bC, 0, by rw [g2]; simp, by omega⟩

set_option maxRecDepth 100000 in
/-- **The loads of `5530 ..< 5564`** read `claim_pool`. -/
theorem vtZt_inBuf {rd : Reader} {w : ℕ → E} {args : List E} {bufs : List (E × ℕ)}
    (b15 : (vtσ rd w args (.n 15), 159) ∈ bufs) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop 5530).take 34) := by
  have e := tbStmtsEqb_sound zTail_at
  have hlen : zTail.length = 34 := rfl
  rw [← hlen, ← e]
  intro d p off hm
  simp only [zTail, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, false_or,
    or_false, List.not_mem_nil] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact vt_inBuf_direct b15 (by norm_num)

end
end LeanVM.Guest.B1.Tables
