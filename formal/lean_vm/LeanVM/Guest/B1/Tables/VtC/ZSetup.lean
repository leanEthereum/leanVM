/-
  LeanVM.Guest.B1.Tables.VtC.ZSetup

  `verify_tables`' statements `g_zc_n ..< x@9`, completely: the table sumcheck's round count, its
  batching challenge and target, its rounds and its equality prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZBase
public import LeanVM.Guest.B1.Eq.EqPrefixRev
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The table sumcheck's setup, completely

Helpers for the honest valuation: a read of a word the memory holds (`z_read`), a product read
as a quotient (`z_div`), a passing range check (`z_rc`, `z_rcd`), a `KECCAK` (`z_keccak`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section Helpers
variable {rd : Reader} {σ : Val}

/-- A read of a word the memory holds. -/
theorem z_read {d p : V} {off : ℕ} {v : E}
    (hg : Atom.load d p off ∈ vtSL ∨ σ d = rdAt rd (σ p) off) (hS : Atom.load d p off ∉ vtSL)
    (hm : LoadHolds rd (σ p) off v) : σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e : σ d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  exact ⟨e, by show LoadHolds rd _ _ _; rw [e]; exact hm⟩

/-- A product read as a quotient. -/
theorem z_div {d x y : V} (hg : σ x = σ d * (σ y)⁻¹) (hy : σ y ≠ 0) :
    (Atom.mul d x y).Holds rd σ := by
  show σ d = σ x * σ y
  rw [hg, mul_assoc, inv_mul_cancel₀ hy, mul_one]

theorem z_gen_addr (a : ℕ) : (gen ^ a).limb 0 * Parameters.addressOfIndex 0 =
    Parameters.addressOfIndex a := by
  rw [gen_pow_eq_ofK]; simp [Parameters.addressOfIndex]

theorem z_low_load {a : ℕ} (h : (rd (Parameters.addressOfIndex a)).isSome) :
    LoadHolds rd (gen ^ a) 0 (rdAt rd (gen ^ a) 0) :=
  load_of_rdAt rfl (gen_pow_isInK a) (by rw [z_gen_addr]; exact h)

/-- **A passing range check**: `x = g^a`, `a ≤ K`, `k = g^K`, on a memory defined at `g^a` and
`g^(K - a)`. -/
theorem z_rc {x y t1 t2 k : V} {a K : ℕ} (haK : a ≤ K) (hx : σ x = gen ^ a) (hk : σ k = gen ^ K)
    (hg : σ t1 = rdAt rd (σ x) 0 ∧ σ t2 = rdAt rd (σ y) 0 ∧ σ y = σ k * (σ x)⁻¹)
    (h1 : (rd (Parameters.addressOfIndex a)).isSome) (h2 : (rd (Parameters.addressOfIndex (K -
        a))).isSome) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ := by
  obtain ⟨e1, e2, ey⟩ := hg
  have ey' : σ y = gen ^ (K - a) := by rw [ey, hk, hx, ← pow_sub₀ _ gen_ne_zero haK]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, hx]; exact z_low_load h1
  · rw [hk, hx, ey', ← pow_add, Nat.add_sub_cancel' haK]
  · rw [e2, ey']; exact z_low_load h2

/-- A range check's facts, as `eq_prefix_chain_rev` states them. -/
theorem z_rcd {a K : ℕ} (haK : a ≤ K) (h1 : (rd (Parameters.addressOfIndex a)).isSome)
    (h2 : (rd (Parameters.addressOfIndex (K - a))).isSome) : RangeChecked rd (gen ^ a) (gen ^ K) :=
  ⟨gen ^ (K - a), _, _, z_low_load h1, by rw [← pow_add, Nat.add_sub_cancel' haK],
    z_low_load h2⟩

/-- **A `KECCAK`** holds by its equations. -/
theorem z_keccak {S : List Atom} {w : ℕ → E} {ins outs : List V} {i o : Bool}
    (hg : Good rd S w σ (.keccak ins outs i o)) : (Atom.keccak ins outs i o).Holds rd σ :=
  holds_of_good hg trivial

theorem z_w32 : word 4294967296 0 = gen ^ 32 := by
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, word_two_pow (by norm_num)]

end Helpers

/-- The bus target: `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` on the sides' totals. -/
def zTarget (σ : Val) (ξ : E) : E :=
  ξ ^ 2 * σ (.n (val% «verify_tables» "bus_table_total[0]")) + ξ ^ 3 * σ (.n (val% «verify_tables» "bus_table_total[1]")) + ξ ^ 4 * σ (.n (val% «verify_tables» "bus_table_total[2]"))

/-- What statements `g_zc_n ..< x@9` give: `g^n`, `ξ` (the squeeze of `S`), the sponge after it,
the target, the buffers' sizes and pointers, and the last record (the sponge, the cursor `3n`
words on, the final claim). -/
def ZOut (σ : Val) (w : ℕ → E) (S : Fs) (xs : List E) (n : ℕ) : Prop :=
  σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n ∧ σ (.n (val% «verify_tables» "nxt[0]@3")) = S.squeeze.1 ∧
    [σ (.n (val% «verify_tables» "nxt[8]@3")), σ (.n (val% «verify_tables» "nxt[9]@3")), σ (.n (val% «verify_tables» "nxt[10]@3")), σ (.n (val% «verify_tables» "nxt[11]@3")), σ (.n (val% «verify_tables» "nxt[12]@3"))] = S.squeeze.2.cap ∧
    σ (.n (val% «verify_tables» "bus_target@3")) = zTarget σ S.squeeze.1 ∧ σ (.n (val% «verify_tables» "zc_rounds")) = w 2316 ∧
    σ (.n (val% «verify_tables» "zc_cprod")) = w 2317 ∧ σ (.n (val% «verify_tables» "zc_rk")) = w 2321 ∧ σ (.n (val% «verify_tables» "zc_peq")) = w 2337 ∧
    [σ (.n (val% «verify_tables» "fs_load.sp[0]")), σ (.n (val% «verify_tables» "fs_load.sp[1]")), σ (.n (val% «verify_tables» "fs_load.sp[2]")), σ (.n (val% «verify_tables» "fs_load.sp[3]")), σ (.n (val% «verify_tables» "fs_load.sp[4]"))] =
      (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).1 ∧
    σ (.n (val% «verify_tables» "cursor@5")) = σ (.n (val% «verify_tables» "cursor@4")) * gen * gen ^ (3 * n) ∧
    σ (.n (val% «verify_tables» "claim")) = (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).2

/-- The statements evaluation alone does not settle. -/
noncomputable def zRest : List Stmt := [
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u0.s1#1")) (.n (val% «verify_tables» "kb[2]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s57.u0.s1#1")) (.n (val% «verify_tables» "s57.u0.s1#2")) (.n (val% «verify_tables» "s57.u0.s1#3")) (.n (val% «verify_tables» "s57.u0.s1#4")) (.n (val% «verify_tables» "s57.u0.s1#0"))),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u1.s1#1")) (.n (val% «verify_tables» "kb[3]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s57.u1.s1#1")) (.n (val% «verify_tables» "s57.u1.s1#2")) (.n (val% «verify_tables» "s57.u1.s1#3")) (.n (val% «verify_tables» "s57.u1.s1#4")) (.n (val% «verify_tables» "s57.u1.s1#0"))),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u2.s1#1")) (.n (val% «verify_tables» "kb[4]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s57.u2.s1#1")) (.n (val% «verify_tables» "s57.u2.s1#2")) (.n (val% «verify_tables» "s57.u2.s1#3")) (.n (val% «verify_tables» "s57.u2.s1#4")) (.n (val% «verify_tables» "s57.u2.s1#0"))),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u3.s1#1")) (.n (val% «verify_tables» "kb[5]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s57.u3.s1#1")) (.n (val% «verify_tables» "s57.u3.s1#2")) (.n (val% «verify_tables» "s57.u3.s1#3")) (.n (val% «verify_tables» "s57.u3.s1#4")) (.n (val% «verify_tables» "s57.u3.s1#0"))),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u4.s1#1")) (.n (val% «verify_tables» "kb[6]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s57.u4.s1#1")) (.n (val% «verify_tables» "s57.u4.s1#2")) (.n (val% «verify_tables» "s57.u4.s1#3")) (.n (val% «verify_tables» "s57.u4.s1#4")) (.n (val% «verify_tables» "s57.u4.s1#0"))),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u5.s1#1")) (.n (val% «verify_tables» "kb[7]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s57.u5.s1#1")) (.n (val% «verify_tables» "s57.u5.s1#2")) (.n (val% «verify_tables» "s57.u5.s1#3")) (.n (val% «verify_tables» "s57.u5.s1#4")) (.n (val% «verify_tables» "s57.u5.s1#0"))),
    .atom (.assertEq (.n (val% «verify_tables» "zc_is_a_tau@6")) (.n (val% «verify_tables» "s58#0"))),
    .atom (.mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s59#1")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s59#1")) (.n (val% «verify_tables» "s59#2")) (.n (val% «verify_tables» "s59#3")) (.n (val% «verify_tables» "s59#4")) (.n (val% «verify_tables» "s59#0"))),
    .atom (.keccak [.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"), .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] [.n (val% «verify_tables» "nxt[0]@3"), .n (val% «verify_tables» "nxt[1]@3"), .n (val% «verify_tables» "nxt[2]@3"), .n (val% «verify_tables» "nxt[3]@3"), .n (val% «verify_tables» "nxt[4]@3"), .n (val% «verify_tables» "nxt[5]@3"), .n (val% «verify_tables» "nxt[6]@3"), .n (val% «verify_tables» "nxt[7]@3"), .n (val% «verify_tables» "nxt[8]@3"), .n (val% «verify_tables» "nxt[9]@3"), .n (val% «verify_tables» "nxt[10]@3"), .n (val% «verify_tables» "nxt[11]@3"), .n (val% «verify_tables» "nxt[12]@3")] false false),
    .atom (.load (.n (val% «verify_tables» "nxt[8]@3")) (.n (val% «verify_tables» "zc_rounds")) 0),
    .atom (.load (.n (val% «verify_tables» "nxt[9]@3")) (.n (val% «verify_tables» "zc_rounds")) 1),
    .atom (.load (.n (val% «verify_tables» "nxt[10]@3")) (.n (val% «verify_tables» "zc_rounds")) 2),
    .atom (.load (.n (val% «verify_tables» "nxt[11]@3")) (.n (val% «verify_tables» "zc_rounds")) 3),
    .atom (.load (.n (val% «verify_tables» "nxt[12]@3")) (.n (val% «verify_tables» "zc_rounds")) 4),
    .atom (.load (.n (val% «verify_tables» "s69#1")) (.n (val% «verify_tables» "zc_rounds")) 5),
    .atom (.load (.n (val% «verify_tables» "bus_target@3")) (.n (val% «verify_tables» "zc_rounds")) 6),
    .atom (.load (.n (val% «verify_tables» "s71#0")) (.n (val% «verify_tables» "zc_cprod")) 0),
    .callIf (.n (val% «verify_tables» "s73#1")) name% «verify_tables_loop0» [.n (val% «verify_tables» "s73#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"), .n (val% «verify_tables» "tabs"), .n (val% «verify_tables» "zc_rk"),
        .n (val% «verify_tables» "zc_cprod")],
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[0]")) (.n (val% «verify_tables» "zc_last")) 0),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[1]")) (.n (val% «verify_tables» "zc_last")) 1),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[2]")) (.n (val% «verify_tables» "zc_last")) 2),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[3]")) (.n (val% «verify_tables» "zc_last")) 3),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[4]")) (.n (val% «verify_tables» "zc_last")) 4),
    .atom (.load (.n (val% «verify_tables» "cursor@5")) (.n (val% «verify_tables» "zc_last")) 5),
    .atom (.load (.n (val% «verify_tables» "claim")) (.n (val% «verify_tables» "zc_last")) 6),
    .call "eq_prefix_chain_rev" [.n (val% «verify_tables» "zc_peq"), .n (val% «verify_tables» "chi"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "g_zc_n")] []]

set_option maxRecDepth 100000 in
/-- **Statements `g_zc_n ..< x@9`, completely** (G:2261-2315): the hinted `g^n` with `n` the
largest `τ_t` (at most `m = |point|`), the squeeze `ξ` (`XI_GRIND_BITS = 0`) of the sponge `S`
with the bytecode's value waiting, the target, the first record, `verify_tables_loop0`'s rounds on
the honest buffers (records, running products, `chi`) and words `xs` at the cursor one past the
bytecode's
value, the last record, `eq_prefix_chain_rev` copying `zc_rk` reversed into `chi` and its prefix
weights against `zeta1`. -/
theorem vtZ_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 21)
    {m n : ℕ} {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t ≤ n) (hτn : ∃ t < 6, τ t = n) (hnm : n ≤ m)
    (hm : m ≤ 32) (h9 : vtσ rd w args (.n (val% «verify_tables» "g_bus_mu")) = gen ^ m)
    (hkb : ∀ t < 6, vtσ rd w args (.n ((val% «verify_tables» "kb[2]") + t)) = gen ^ τ t)
    (hlow : ∀ i < 64, (rd (Parameters.addressOfIndex i)).isSome) (hwn : w 2240 = gen ^ n) {S : Fs}
    (hSr : rateOf S.pend = [vtσ rd w args (.n (val% «verify_tables» "rate[0]@3")), vtσ rd w args (.n (val% «verify_tables» "rate[1]@3")), 0, 0, 0, 0, 0, 0])
    (hSc : S.cap = [vtσ rd w args (.n (val% «verify_tables» "sp[0]@2")), vtσ rd w args (.n (val% «verify_tables» "sp[1]@2")), vtσ rd w args (.n (val% «verify_tables» "sp[2]@2")),
      vtσ rd w args (.n (val% «verify_tables» "sp[3]@2")), vtσ rd w args (.n (val% «verify_tables» "sp[4]@2"))])
    {xs : List E} (hxl : xs.length = 3 * n)
    (hxs : ReadsAt rd (vtσ rd w args (.n (val% «verify_tables» "cursor@4")) * gen) xs)
    (hR : ReadsAt rd (w 2316) (zcRoundsW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1)
      (vtσ rd w args (.n (val% «verify_tables» "cursor@4")) * gen) xs n))
    (hC : ReadsAt rd (w 2317)
      (zcCprodW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    (hrk : ReadsAt rd (w 2321) (zcRkW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    (hchi : ReadsAt rd (vtσ rd w args (.n (val% «verify_tables» "chi")))
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    {zs1 : List E} (hz1 : ReadsAt rd (vtσ rd w args (.n (val% «verify_tables» "zeta1"))) zs1) (hz1l : n ≤ zs1.length)
    (hP : ReadsAt rd (w 2337) ((List.range (n + 1)).map (prefixProd 1
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n) (zs1.take n)))) :
    (∀ s ∈ (vtPre.drop (pos% «verify_tables» "g_zc_n")).take (span% «verify_tables» "g_zc_n" "x@9"), VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n := by
  have g : GoodL rd w (vtσ rd w args) zBlk := vt_goodL hl 2286 zBlk zBlk_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"),
      .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] (lyOuts (val% «verify_tables» "nxt[0]@3")) false false) :=
    (vt_goodL (rd := rd) (w := w) hl 2326 [.atom (.keccak [.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"),
      .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")]
      (lyOuts (val% «verify_tables» "nxt[0]@3")) false false)] (by decide +kernel)).1
  have e := stmtsEqb_sound zBlk_at
  have hlen : zBlk.length = 83 := rfl
  suffices H : (∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen, ← e] at hs
    exact vt_block hl 2286 zBlk zBlk_at zRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zBlk, GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    and_false, ↓reduceIte] at g
  obtain ⟨g2590, g2591, g2592, g2593, g2594, g2595, g2596, g2597, g2598, g2599, g2600, g2601, g2602, g2603,
    g2604, g2605, g2606, g2607, g2608, g2609, g2610, g2611, g2612, g2613, g2614, g2615, g2616, g2617, g2618,
    g2619, g2620, g2621, g2622, g2623, g2624, g2625, g2626, g2627, g2628, g2629, g2630, g2631, g2632, g2633,
    g2634, g2635, g2636, g2637, g2638, g2639, g2640, g2641, g2642, g2643, g2644, g2645, g2646, g2647, g2648,
    g2649, g2650, g2651, g2652, g2653, g2654, g2655, g2656, g2657, g2658, g2659, g2660, g2661, g2662, g2663,
    g2664, g2665, g2666, g2667, g2668, g2669, g2670, g2671, g2672⟩ := g
  have vn : σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n := g2590.1.trans hwn
  -- n dominates every τ_t
  have hx : ∀ {t d : ℕ}, t < 6 → σ (.n d) = σ (.n (val% «verify_tables» "g_zc_n")) * (σ (.n (28 + t)))⁻¹ →
      σ (.n d) = gen ^ (n - τ t) ∧ σ (.n (28 + t)) ≠ 0 := fun {t d} ht hg ↦ by
    rw [hkb t ht] at hg ⊢
    exact ⟨by rw [hg, vn, ← pow_sub₀ _ gen_ne_zero (hτ t ht)], pow_ne_zero _ gen_ne_zero⟩
  obtain ⟨x0, n0⟩ := hx (t := 0) (by norm_num) g2592
  obtain ⟨x1, n1⟩ := hx (t := 1) (by norm_num) g2596
  obtain ⟨x2, n2⟩ := hx (t := 2) (by norm_num) g2601
  obtain ⟨x3, n3⟩ := hx (t := 3) (by norm_num) g2606
  obtain ⟨x4, n4⟩ := hx (t := 4) (by norm_num) g2611
  obtain ⟨x5, n5⟩ := hx (t := 5) (by norm_num) g2616
  have rc2574 := z_rc (a := n - τ 0) (K := 32) (by omega) x0 (g2591.trans z_w32) g2593
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2578 := z_rc (a := n - τ 1) (K := 32) (by omega) x1 (g2595.trans z_w32) g2597
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2583 := z_rc (a := n - τ 2) (K := 32) (by omega) x2 (g2600.trans z_w32) g2602
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2588 := z_rc (a := n - τ 3) (K := 32) (by omega) x3 (g2605.trans z_w32) g2607
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2593 := z_rc (a := n - τ 4) (K := 32) (by omega) x4 (g2610.trans z_w32) g2612
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2598 := z_rc (a := n - τ 5) (K := 32) (by omega) x5 (g2615.trans z_w32) g2617
    (hlow _ (by omega)) (hlow _ (by omega))
  have m2573 := z_div (rd := rd) g2592 n0
  have m2577 := z_div (rd := rd) g2596 n1
  have m2582 := z_div (rd := rd) g2601 n2
  have m2587 := z_div (rd := rd) g2606 n3
  have m2592 := z_div (rd := rd) g2611 n4
  have m2597 := z_div (rd := rd) g2616 n5
  -- n ≤ m
  have x6 : σ (.n (val% «verify_tables» "s59#1")) = gen ^ (m - n) := by
    rw [g2623, h9, vn, ← pow_sub₀ _ gen_ne_zero hnm]
  have rc2605 := z_rc (a := m - n) (K := 32) (by omega) x6 (g2622.trans z_w32) g2624
    (hlow _ (by omega)) (hlow _ (by omega))
  have m2604 := z_div (rd := rd) g2623 (by rw [vn]; exact pow_ne_zero _ gen_ne_zero)
  -- some τ_t is n
  have hz : σ (.n (val% «verify_tables» "zc_is_a_tau@6")) = 0 := by
    rw [g2619, g2614, g2609, g2604, g2599, g2594, g2598, g2603, g2608, g2613, g2618, vn,
      hkb 0 (by norm_num), hkb 1 (by norm_num), hkb 2 (by norm_num), hkb 3 (by norm_num),
      hkb 4 (by norm_num), hkb 5 (by norm_num)]
    obtain ⟨t, ht, hte⟩ := hτn
    interval_cases t <;> simp [hte, CharTwo.add_self_eq_zero]
  have a2602 : (Atom.assertEq (.n (val% «verify_tables» "zc_is_a_tau@6")) (.n (val% «verify_tables» "s58#0"))).Holds rd σ := by
    show σ (.n (val% «verify_tables» "zc_is_a_tau@6")) + σ (.n (val% «verify_tables» "s58#0")) = 0
    rw [hz, g2620, word_zero, add_zero]
  -- the squeeze
  have hz0 : σ (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]")) = 0 := g2626.trans word_zero
  have hz1' : σ (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]")) = 0 := g2627.trans word_zero
  have hz2 : σ (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]")) = 0 := g2628.trans word_zero
  have hz3 : σ (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]")) = 0 := g2629.trans word_zero
  have hin : ([.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"),
      .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] : List V).map σ = rateOf S.pend ++ S.cap := by
    rw [hSr, hSc]; simp [hz0, hz1', hz2, hz3]
  have k2631 : (Atom.keccak [.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"),
      .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] (lyOuts (val% «verify_tables» "nxt[0]@3")) false false).Holds rd σ := z_keccak gk
  obtain ⟨hPk, -⟩ := ly_keccak k2631
  rw [hin] at hPk
  have vξ : σ (.n (val% «verify_tables» "nxt[0]@3")) = S.squeeze.1 := challengeT_value (s0 := .n (val% «verify_tables» "nxt[0]@3")) (b := 2293) rfl (hPk 0 (by norm_num))
  have hcap0 : [σ (.n (val% «verify_tables» "nxt[8]@3")), σ (.n (val% «verify_tables» "nxt[9]@3")), σ (.n (val% «verify_tables» "nxt[10]@3")), σ (.n (val% «verify_tables» "nxt[11]@3")), σ (.n (val% «verify_tables» "nxt[12]@3"))] =
      S.squeeze.2.cap := by
    rw [hPk 8 (by norm_num), hPk 9 (by norm_num), hPk 10 (by norm_num), hPk 11 (by norm_num),
      hPk 12 (by norm_num)]
    rfl
  have vT : σ (.n (val% «verify_tables» "bus_target@3")) = zTarget σ S.squeeze.1 := by
    rw [g2640, g2638, g2636, g2637, g2639, g2635, g2634, g2633, g2632, g2631, word_one, vξ,
      zTarget]
    ring
  -- the buffers
  set cap0 := S.squeeze.2.cap with hcap0d
  set cl0 := zTarget σ S.squeeze.1 with hcl0d
  have h5 : cap0.length = 5 := rfl
  have v2589 : σ (.n (val% «verify_tables» "zc_rounds")) = w 2316 := g2641
  have v2592 : σ (.n (val% «verify_tables» "zc_cprod")) = w 2317 := g2642
  have v2613 : σ (.n (val% «verify_tables» "zc_peq")) = w 2337 := g2671
  have r0 := zcRoundsW_reads h5 hR 0 (by omega)
  rw [Nat.mul_zero, pow_zero, mul_one, zcRecW, ← v2589] at r0
  simp only [zcRec, Nat.mul_zero, pow_zero, mul_one, ← hcap0, ← vT] at r0
  have v2594 : σ (.n (val% «verify_tables» "s69#1")) = σ (.n (val% «verify_tables» "cursor@4")) * gen := by
    rw [g2649, g2648, word_gen]
  have s2650 : (Atom.load (.n (val% «verify_tables» "s71#0")) (.n (val% «verify_tables» "zc_cprod")) 0).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g2652, word_one, v2592]
    simpa [zcCprodW] using hC 0 (by simp [zcCprodW])
  -- the rounds
  have v2635 : σ (.n (val% «verify_tables» "zc_rk")) = w 2321 := g2654
  have v2597 : σ (.n (val% «verify_tables» "s73#1")) = 1 + gen ^ n := by rw [g2656, g2655, word_one, vn]
  have c2654 : VSH (coreProgram.Rel rd) rd σ
      (.callIf (.n (val% «verify_tables» "s73#1")) name% «verify_tables_loop0» [.n (val% «verify_tables» "s73#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"), .n (val% «verify_tables» "tabs"), .n (val% «verify_tables» "zc_rk"),
          .n (val% «verify_tables» "zc_cprod")]) := by
    refine ⟨by rw [v2597]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n),
      fun hne => ?_⟩
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (by rw [v2597, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
      · exact h
    simp only [List.map_cons, List.map_nil]
    rw [g2657, word_one, vn, v2589, v2592, v2635]
    exact l10_complete hn0 (zc_l10B h5 hR hC hrk hxs hxl)
  -- the last record
  have v2603 : σ (.n (val% «verify_tables» "zc_last")) = w 2316 * gen ^ (7 * n) := by
    rw [g2663, g2662, g2661, g2660, g2659, vn, v2589]; ring
  have rn := zcRoundsW_reads h5 hR n le_rfl
  rw [zcRecW, ← v2603] at rn
  have hlen := zcRec_len (cl0 := cl0) (xs := xs) h5 n
  obtain ⟨e0, r2660⟩ := z_read g2664 (by decide +kernel) (rn 0 (by simp [hlen]))
  obtain ⟨e1, r2661⟩ := z_read g2665 (by decide +kernel) (rn 1 (by simp [hlen]))
  obtain ⟨e2, r2662⟩ := z_read g2666 (by decide +kernel) (rn 2 (by simp [hlen]))
  obtain ⟨e3, r2663⟩ := z_read g2667 (by decide +kernel) (rn 3 (by simp [hlen]))
  obtain ⟨e4, r2664⟩ := z_read g2668 (by decide +kernel) (rn 4 (by simp [hlen]))
  obtain ⟨e5, r2665⟩ := z_read g2669 (by decide +kernel) (rn 5 (by simp [hlen]))
  obtain ⟨e6, r2666⟩ := z_read g2670 (by decide +kernel) (rn 6 (by simp [hlen]))
  -- the equality prefix
  have c2671 : VSH (coreProgram.Rel rd) rd σ
      (.call "eq_prefix_chain_rev" [.n (val% «verify_tables» "zc_peq"), .n (val% «verify_tables» "chi"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "g_zc_n")] []) := by
    show coreProgram.Rel rd _ _ _
    simp only [List.map_cons, List.map_nil]
    rw [vn, v2613, v2635]
    refine (eq_prefix_chain_rev_holds rd _ _).mpr ⟨rfl, z_rcd (by omega) (hlow _ (by omega))
      (hlow _ (by omega)), n, by omega, rfl, zc_chiRev hrk hchi, zcChis cap0 cl0 xs n, zs1.take n,
      by simp [zcChis, zcRkW],
      by simp; omega, hchi, fun k hk => by rw [List.getElem_take]; exact hz1 _ _, fun j hj => ?_⟩
    have := hP j (by simp; omega)
    simpa using this
  -- the statements
  have s2640 : (Atom.load (.n (val% «verify_tables» "nxt[8]@3")) (.n (val% «verify_tables» "zc_rounds")) 0).Holds rd σ := r0 0 (by simp)
  have s2641 : (Atom.load (.n (val% «verify_tables» "nxt[9]@3")) (.n (val% «verify_tables» "zc_rounds")) 1).Holds rd σ := r0 1 (by simp)
  have s2642 : (Atom.load (.n (val% «verify_tables» "nxt[10]@3")) (.n (val% «verify_tables» "zc_rounds")) 2).Holds rd σ := r0 2 (by simp)
  have s2643 : (Atom.load (.n (val% «verify_tables» "nxt[11]@3")) (.n (val% «verify_tables» "zc_rounds")) 3).Holds rd σ := r0 3 (by simp)
  have s2644 : (Atom.load (.n (val% «verify_tables» "nxt[12]@3")) (.n (val% «verify_tables» "zc_rounds")) 4).Holds rd σ := r0 4 (by simp)
  have s2647 : (Atom.load (.n (val% «verify_tables» "s69#1")) (.n (val% «verify_tables» "zc_rounds")) 5).Holds rd σ := by
    show LoadHolds rd _ _ _; rw [v2594]; exact r0 5 (by simp)
  have s2648 : (Atom.load (.n (val% «verify_tables» "bus_target@3")) (.n (val% «verify_tables» "zc_rounds")) 6).Holds rd σ := r0 6 (by simp)
  have hrest : ∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl := hs
    · exact m2573
    · exact rc2574
    · exact m2577
    · exact rc2578
    · exact m2582
    · exact rc2583
    · exact m2587
    · exact rc2588
    · exact m2592
    · exact rc2593
    · exact m2597
    · exact rc2598
    · exact a2602
    · exact m2604
    · exact rc2605
    · exact k2631
    · exact s2640
    · exact s2641
    · exact s2642
    · exact s2643
    · exact s2644
    · exact s2647
    · exact s2648
    · exact s2650
    · exact c2654
    · exact r2660
    · exact r2661
    · exact r2662
    · exact r2663
    · exact r2664
    · exact r2665
    · exact r2666
    · exact c2671
  refine ⟨hrest, vn, vξ, hcap0, vT, v2589, v2592, v2635, v2613, ?_, ?_, ?_⟩
  · change [σ (.n (val% «verify_tables» "fs_load.sp[0]")), σ (.n (val% «verify_tables» "fs_load.sp[1]")), σ (.n (val% «verify_tables» "fs_load.sp[2]")), σ (.n (val% «verify_tables» "fs_load.sp[3]")), σ (.n (val% «verify_tables» "fs_load.sp[4]"))] =
      (zcRec cap0 cl0 xs n).1
    apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.length_cons, List.length_nil] at h1
    interval_cases k
    · rw [List.getElem_cons_zero, e0, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_zero, e1, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_zero, e2,
        List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
        List.getElem_cons_zero, e3, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
        List.getElem_cons_succ, List.getElem_cons_zero, e4, List.getElem_append_left]
  · rw [e5, List.getElem_append_right (by omega)]; simp [hlen]
  · change σ (.n (val% «verify_tables» "claim")) = (zcRec cap0 cl0 xs n).2
    rw [e6, List.getElem_append_right (by omega)]; simp [hlen]

end
end LeanVM.Guest.B1.Tables
