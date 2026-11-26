/-
  LeanVM.Guest.B1.Tables.VtC.ZInBuf

  Where `verify_tables`' statements `g_zc_n ..< x@9` and `nxt[0]@42 ..< ret` load: the rounds'
  records, the running products, `claim_pool`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZTail
public import LeanVM.Guest.B1.Tables.VtC.InBuf
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The loads, inside buffers

`vtZ_inBuf`: the loads of `g_zc_n ..< x@9`, `n ≤ 34`, read the records (`7(n + 1)` of the `245` words at `w 2316`,
the last one `7n` on) and the running products (of the `35` at `w 2317`).
`vtZt_inBuf`: those of `nxt[0]@42 ..< ret` read `claim_pool` (`159` words).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The loads of `g_zc_n ..< x@9`** read the records and the running products. -/
theorem vtZ_inBuf {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 21) {n : ℕ}
    (hwn : w 2240 = gen ^ n) (hn34 : n ≤ 34) {bufs : List (E × ℕ)}
    (bR : (w 2316, 245) ∈ bufs) (bC : (w 2317, 35) ∈ bufs) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop (pos% «verify_tables» "g_zc_n")).take (span% «verify_tables» "g_zc_n" "x@9")) := by
  have g0 := vt_goodL (rd := rd) (w := w) hl 2286
    [.atom (.hint (.witness "zc_tau_max" (.stack [.n (val% «verify_tables» "g_zc_n")])))] (by decide +kernel)
  have g1 := vt_goodL (rd := rd) (w := w) hl 2337 [.atom (.hint (.alloc (.n (val% «verify_tables» "zc_rounds")) 245))]
    (by decide +kernel)
  have g2 := vt_goodL (rd := rd) (w := w) hl 2338 [.atom (.hint (.alloc (.n (val% «verify_tables» "zc_cprod")) 35))]
    (by decide +kernel)
  have g3 := vt_goodL (rd := rd) (w := w) hl 2355 [.atom (.mul (.n (val% «verify_tables» "zc_last~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.mul (.n (val% «verify_tables» "zc_last~1")) (.n (val% «verify_tables» "zc_last~0")) (.n (val% «verify_tables» "g_zc_n"))), .atom (.mul (.n (val% «verify_tables» "zc_last~2")) (.n (val% «verify_tables» "zc_last~1")) (.n (val% «verify_tables» "zc_last~1"))),
    .atom (.mul (.n (val% «verify_tables» "zc_last~3")) (.n (val% «verify_tables» "zc_last~2")) (.n (val% «verify_tables» "g_zc_n"))), .atom (.mul (.n (val% «verify_tables» "zc_last")) (.n (val% «verify_tables» "zc_rounds")) (.n (val% «verify_tables» "zc_last~3")))]
    (by decide +kernel)
  have e := tbStmtsEqb_sound zBlk_at
  have hlen : zBlk.length = 83 := rfl
  rw [← hlen, ← e]
  generalize vtσ rd w args = σ at *
  simp only [GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    ↓reduceIte] at g0 g1 g2 g3
  obtain ⟨m22, m23, m24, m25, m26⟩ := g3
  have v2589 : σ (.n (val% «verify_tables» "zc_rounds")) = w 2316 := g1
  have v2603 : σ (.n (val% «verify_tables» "zc_last")) = w 2316 * gen ^ (7 * n) := by
    rw [m26, m25, m24, m23, m22, g0.1, hwn, v2589]; ring
  intro d p off hm
  simp only [zBlk, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, false_or,
    or_false, List.not_mem_nil] at hm
  have hR : ∀ k < 7, InBuf σ bufs (.n (val% «verify_tables» "zc_rounds")) k := fun k hk => ⟨_, bR, 0, by rw [v2589]; simp,
    by omega⟩
  have hN : ∀ k < 7, InBuf σ bufs (.n (val% «verify_tables» "zc_last")) k := fun k hk => ⟨_, bR, 7 * n, v2603, by omega⟩
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals first
    | exact hR _ (by norm_num)
    | exact hN _ (by norm_num)
    | exact ⟨_, bC, 0, by rw [g2]; simp, by omega⟩

set_option maxRecDepth 100000 in
/-- **The loads of `nxt[0]@42 ..< ret`** read `claim_pool`. -/
theorem vtZt_inBuf {rd : Reader} {w : ℕ → E} {args : List E} {bufs : List (E × ℕ)}
    (b15 : (vtσ rd w args (.n (val% «verify_tables» "claim_pool")), 159) ∈ bufs) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop (pos% «verify_tables» "nxt[0]@42")).take (span% «verify_tables» "nxt[0]@42" "ret")) := by
  have e := tbStmtsEqb_sound zTail_at
  have hlen : zTail.length = 31 := rfl
  rw [← hlen, ← e]
  intro d p off hm
  simp only [zTail, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, false_or,
    or_false, List.not_mem_nil] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact vt_inBuf_direct b15 (by norm_num)

end
end LeanVM.Guest.B1.Tables
