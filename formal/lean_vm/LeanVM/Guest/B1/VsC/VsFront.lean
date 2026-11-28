/-
  LeanVM.Guest.B1.VsC.VsFront

  `verify_sub`'s windows before `wC`, composed from the phases.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh3

/-!
# `verify_sub`'s front

`VsHyp`'s windows before `wC` (`wA`, the least-height branch, `wB`, the pointer width's branch) from the phases'
lemmas (`vsPh0_wins`, `vsPh1_wins`, `vsPh2_wins`, `vsPh2_sel`, `vsPh3_wins`) by `winsHyp_append`, on one set of
numeric hypotheses: the stream `ws` of `p` chunks, the rate `r`, the memory's log `m`, the tables' log heights
`h` and row counts `Rr`, the link's width `wd`, its flag and the cycle count `N = Σ Rr`; what the evaluation
memory and every memory holding the node's words read (`FrontReads`); the node's own cells. Every callee of the
front is a leaf ending at its cursor, so the callees' cursor after it is explicit (`frontKc`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- The callees' cursor after `wA`: `hint_stream` of `p` chunks, two `g_power_of_word`s, six `table_size`s. -/
def frontKc (fs : String → ℕ) (al : String → Bool) (p : ℕ) (h : ℕ → ℕ) (kc : ℕ) : ℕ :=
  tsEnd fs al h (leafEnd fs al "g_power_of_word" (leafEnd fs al "g_power_of_word"
    (allocBase (al hsLoopName) (allocBase (al "hint_stream") kc + fs "hint_stream") + hsB fs p)))

/-- The rows' word list: the tables' row counts. -/
def rowsW (Rr : ℕ → ℕ) : List E :=
  [eOfNat (Rr 0), eOfNat (Rr 1), eOfNat (Rr 2), eOfNat (Rr 3), eOfNat (Rr 4), eOfNat (Rr 5)]

/-- The heights' word list. -/
def heightsW (h : ℕ → ℕ) : List E := [gen ^ h 0, gen ^ h 1, gen ^ h 2, gen ^ h 3, gen ^ h 4, gen ^ h 5]

/-- **What the front reads of a memory**: the stream at `a + 824`, the row counts after it, the heights at
`b6`, the eight-word buffer after the row counts, the bits' buffers at `b7`, the cycle count's bits at `b8`,
the link's shape at `b9`. -/
structure FrontReads (rd : Reader) (a p : ℕ) (ws : List E) (b6 b7 b8 b9 m : ℕ) (h Rr : ℕ → ℕ) (n wd : ℕ)
    (flag f4 : E) : Prop where
  stream : ReadsAt rd (ptrAt (a + 824)) ws
  sizes : ReadsAt rd (ptrAt (a + (824 + 256 * p))) (rowsW Rr)
  heights : ReadsAt rd (ptrAt b6) (heightsW h)
  logs : ReadsAt rd (ptrAt (a + (824 + 256 * p) + 6)) (1 :: gen ^ m :: heightsW h)
  bits : ∀ t < 6, ReadsAt rd (ptrAt (b7 + 26 * t)) (tsBitsW (Rr t) (h t))
  cycles : ReadsAt rd (ptrAt b8) (cbL (Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5))
  shape : ReadsAt rd (ptrAt b9) [gen ^ n, gen ^ wd, flag, f4]

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`verify_sub`'s front's windows' hypotheses**: `wA`, the least-height branch, `wB` and the pointer
width's branch from the numeric facts of the node; `KC` after either arm of the last branch, at the callees'
cursor past `frontKc` and one or two `assert_small_g_power` leaves. -/
theorem vsFront_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {KC : St → Prop}
    {p r m n wd b6 b7 b8 b9 qt : ℕ} {flag f4 : E} (ws : List E) (h Rr : ℕ → ℕ)
    (hp1 : 1 ≤ p) (hp : p ≤ 32) (hws : ws.length = 256 * p) (hw7r : ws.getD 7 0 = eOfNat r)
    (hw0m : ws.getD 0 0 = eOfNat m) (hws56 : (ws.drop 1).take 6 = rowsW Rr)
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (hm1 : 1 ≤ m)
    (h24 : ∀ t < 6, h t ≤ 24) (hR : ∀ t < 6, Rr t ≤ 2 ^ h t) (hl : ∀ t < 5, h t = 0 ∨ 2 ^ (h t - 1) < Rr t)
    (h9 : 9 ≤ h 5) (hl5 : h 5 ≠ 9 → 2 ^ (h 5 - 1) < Rr 5)
    (hht : ∀ t < 6, h t ≤ n) (hn : ∃ t < 6, h t = n)
    (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24) (hmw : m ≤ wd) (hN : Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5 < 2 ^ wd)
    (hflag : (flag = 1 ∧ 2 ^ (wd - 1) ≤ Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5) ∨
      (flag = 0 ∧ (wd = m ∨ wd = 19)))
    (hw42 : w 42 = gen ^ p)
    (hwA : [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w =
      (bases st.a (vsSz0 ++ [256 * p])).map (fun b => ofK (addressOfIndex b)))
    (hw6 : w 6 = ptrAt b6) (hw7 : w 7 = ptrAt b7) (hw8 : w 8 = ptrAt b8) (hw9 : w 9 = ptrAt b9)
    (hw55 : w 55 = ptrAt (st.a + 824)) (hw56 : w 56 = ptrAt (st.a + (824 + 256 * p)))
    (hw112 : w 112 = ptrAt (st.a + (824 + 256 * p) + 6)) (hw94 : w 94 = gen ^ r) (hw101 : w 101 = gen ^ m)
    (hret : ∀ t < 6, w (tsRet t) = gen ^ Rr t ∧ w (tsRet t + 1) = tsLeadW (Rr t) (h t) ∧
      w (tsRet t + 2) = tsRestW (Rr t) (h t))
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt)
    (r0 : FrontReads rd0 st.a p ws b6 b7 b8 b9 m h Rr n wd flag f4) (rq : ExpTables rd0 (ptrAt qt))
    (hO : ∀ rd, st.O rd → FrontReads rd st.a p ws b6 b7 b8 b9 m h Rr n wd flag f4)
    (hOwn : ∀ i, st.a + 824 ≤ i → i < st.a + 824 + 256 * p + 14 → Own i)
    (hO6 : ∀ j < 6, Own (b6 + j)) (hO7 : ∀ j < 156, Own (b7 + j)) (hO8 : ∀ j < 24, Own (b8 + j))
    (hO9 : ∀ j < 4, Own (b9 + j)) (hRq : ∀ j < 178, R (qt + j)) (hPre : ∀ rd, Pre rd → ExpTables rd (ptrAt qt))
    (hKz : flag = 1 → KC ⟨st.a + (824 + 256 * p) + 14,
      leafEnd fs al "assert_small_g_power" (leafEnd fs al "assert_small_g_power" (frontKc fs al p h st.kc)),
      st.O, st.D, st.Qs ++ hsQ ws p :: List.replicate 10 PostQuiet⟩)
    (hKn : flag = 0 → KC ⟨st.a + (824 + 256 * p) + 14,
      leafEnd fs al "assert_small_g_power" (frontKc fs al p h st.kc), st.O, st.D, st.Qs ++ hsQ ws p :: List.replicate 9 PostQuiet⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wA st (fun s1 =>
      IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 234) [] wI1 s1 fun s2 =>
        WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wB s2 fun s3 =>
          IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 471) wI2z wI2n s3 KC) := by
  have hwl : 10 ≤ ws.length := by rw [hws]; omega
  have eA : wA = [vsA_w0, vsA_w1, vsA_w2] ++ ([vsA_w3, vsA_w4, vsA_w5, vsA_w6] ++ [vsA_w7, vsA_w8, vsA_w9,
      vsA_w10, vsA_w11, vsA_w12, vsA_w13, vsA_w14, vsA_w15, vsA_w16, vsA_w17, vsA_w18]) := rfl
  rw [eA, winsHyp_append]
  -- phase 0
  refine vsPh0_wins hk ha hp hw42 hwA hw55 hw56 ws hws (by omega) r0.stream
    (fun j hj => hOwn _ (by omega) (by omega)) (fun j hj => hOwn _ (by omega) (by omega))
    (fun rd ho => ⟨(hO rd ho).stream, by rw [hws56]; exact (hO rd ho).sizes⟩) ?_
  rw [winsHyp_append]
  -- phase 1
  have hh0 := h24 0 (by norm_num)
  refine vsPh1_wins (h0 := h 0) hk ha hr1 hr4 hm1 (by omega) hw6 hw55 hw56 hw112 hw94 hw101 hh0
    (gen ^ h 1) (gen ^ h 2) (gen ^ h 3) (gen ^ h 4) (gen ^ h 5) ws hwl hw7r hw0m r0.heights r0.stream
    (by rw [hws56]; exact r0.sizes) hO6
    (fun j hj => hOwn (st.a + (824 + 256 * p) + 6 + j) (by omega) (by omega))
    ⟨hOwn _ (by omega) (by omega), hOwn _ (by omega) (by omega)⟩
    (hOwn _ (by omega) (by omega))
    (fun rd ho => ⟨(hO rd ho.1).heights, (hO rd ho.1).logs, (hO rd ho.1).stream,
      by rw [hws56]; exact (hO rd ho.1).sizes⟩) ?_
  -- phase 2
  obtain ⟨v115, v116, v117, v118, v119, v120, -⟩ :=
    vsW6_vals (rd0 := rd0) (w := w) (args := args) ha hw6 hw56 (bs := rowsW Rr) (by simp [rowsW]) r0.heights
      r0.sizes
  refine vsPh2_wins hk ha h Rr h24 hR hl h9 hw6 hw7 hw56 hret r0.heights r0.sizes
    (fun j hj => hOwn _ (by omega) (by omega)) hO7
    (fun rd ho => ⟨(hO rd ho.1.1.1).sizes, fun t ht c hc => by rw [hc]; exact (hO rd ho.1.1.1).bits t ht⟩) ?_
  -- the least-height branch
  have hr5 := hret 5 (by norm_num)
  refine vsPh2_sel ha h9 (h24 5 (by norm_num)) (hR 5 (by norm_num)) hl5 v120 hr5.2.1 hr5.2.2 ?_
  -- phase 3
  obtain ⟨h216, h224⟩ := vsVal_216 (rd0 := rd0) (w := w) ha Rr fun t ht => (hret t ht).1
  have h101 : vsVal rd0 w args (.n 101) = gen ^ m :=
    (vsVal_call_ret ha vsW5_eq (.n 101) (List.mem_singleton_self _)).trans hw101
  have hv : ∀ t < 6, vsVal rd0 w args (.n (115 + t)) = gen ^ h t := by
    intro t ht
    interval_cases t
    exacts [v115, v116, v117, v118, v119, v120]
  have hn24 : n ≤ 24 := by obtain ⟨t, ht, rfl⟩ := hn; exact h24 t ht
  refine vsPh3_wins hk ha h h216 h224 hv h101 h4 hw8 hw9 hht hn hn24 hw19 hw24 hmw hN hflag r0.cycles r0.shape rq
    hO8 hO9 hRq hPre (fun rd ho => ⟨(hO rd ho.1.1.1).cycles, (hO rd ho.1.1.1).shape⟩) ?_ ?_
  · exact fun hf => st_congr (hKz hf) rfl (fun rd => by simp) (fun i => by simp) (by simp [List.replicate])
  · exact fun hf => st_congr (hKn hf) rfl (fun rd => by simp) (fun i => by simp) (by simp [List.replicate])

end

end
end LeanVM.Guest.B1.VsC
