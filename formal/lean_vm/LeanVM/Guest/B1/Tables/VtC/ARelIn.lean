/-
  LeanVM.Guest.B1.Tables.VtC.ARelIn

  **`verify_tables`' calls load from its layout**: on the honest memory and oracle, every
  statement holds with its calls by relations loading from the caller's and the own buffers only.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AMain
public import LeanVM.Guest.B1.Tables.Kids.Families
public import LeanVM.Guest.B1.Tables.Kids.BlockSelTab
public import LeanVM.Guest.B1.Tables.Kids.Shared
public import LeanVM.Guest.B1.Tables.Kids.EqChain
public import LeanVM.Guest.B1.Tables.Kids.Loop10
public import LeanVM.Guest.B1.Eq.EqPrefixRevIn
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»
import LeanVM.Guest.StmtsAppend

/-!
# The calls, placed

`plainStB`: an atom, or an `ite` of atoms, whose `VSH` does not depend on the call relation
(`vsh_plain`). `verify_tables`' other statements are its `119` calls (`vt_calls`, by the kernel):
the padding weights (`pwCall`), `plus_one_run` (`porCall`), the shared selector tables (`shCall`),
the framework blocks' selectors and `index_mle` (`fwCall`, `imCall`), the table blocks' selectors
on their hinted digits (`selCall`), the slot sumcheck's tail rounds (`otrCall`),
`verify_tables_loop0` and `eq_prefix_chain_rev`.

A call's pointers are buffer bases times powers of `g` (from the statements' equations,
`kappa_base` and the shared lengths of `vt_rel_completeF`), inside the buffers (`ptr_lin`,
`ptr_own`), so the callees' `RelIn` lemmas (`Tables/Kids`) apply; `block_selector_tab`'s digits
are `g^u`, `u` a nibble (`offDigits_reads`, `btk_digit`). `vt_relIn_complete`: under
`vt_rel_complete`'s hypotheses, every statement holds by `coreProgram.RelIn` on `RegionL` of the
caller's and the own buffers.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (RegionL)

@[expose] public section

/-! ## Statements without calls -/

/-- An atom. -/
def atomStB : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- An atom, or an `ite` of atoms. -/
def plainStB : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => z.all atomStB && n.all atomStB
  | _ => false

theorem sholds_atom {C C' : CallRel} {rd : Reader} {σ : Val} {s : Stmt} (h : atomStB s = true)
    (hs : SHolds C rd σ s) : SHolds C' rd σ s := by
  cases s with
  | atom a => exact hs
  | _ => simp [atomStB] at h

theorem vsh_plain {C C' : CallRel} {rd : Reader} {σ : Val} {s : Stmt} (h : plainStB s = true)
    (hs : VSH C rd σ s) : VSH C' rd σ s := by
  cases s with
  | atom a => exact hs
  | ite c z n =>
    simp only [plainStB, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨hs.1, fun h0 s hs' ↦ sholds_atom (h.1 s hs') (hs.2.1 h0 s hs'),
      fun h0 s hs' ↦ sholds_atom (h.2 s hs') (hs.2.2 h0 s hs')⟩
  | _ => simp [plainStB] at h

/-- A dispatch on `g^m` by `C` is one by `C'` when arm `m`'s call is. -/
theorem vsh_disp {C C' : CallRel} {rd : Reader} {σ : Val} {x : V} {fs : List String}
    {a r : List V} {m : ℕ} (hx : σ x = gen ^ m) (hm : m < fs.length) (hfs : fs.length ≤ 64)
    (hup : C fs[m] (a.map σ) (r.map σ) → C' fs[m] (a.map σ) (r.map σ))
    (h : VSH C rd σ (.dispatch x fs a r)) : VSH C' rd σ (.dispatch x fs a r) := by
  rw [vsh_dispatch] at h ⊢
  obtain ⟨j, hj, e, hc⟩ := h
  obtain rfl : m = j := by
    rw [hx, gen_pow_eq_ofK] at e
    have := congrArg LeanVM.Guest.Memory.logG e
    rwa [LeanVM.Guest.Memory.logG_spec (e := m) (by omega),
      LeanVM.Guest.Memory.logG_spec (e := j) (by omega)] at this
  exact ⟨m, hm, by rw [hx, gen_pow_eq_ofK], hup hc⟩

/-! ## The calls -/

/-- Table `t`'s `padding_weight` dispatch. -/
def pwCall (t : ℕ) : Stmt :=
  .dispatch (.n (val% «verify_tables» "kb[2]" + t)) vtPadNames [.n (val% «verify_tables» "rows@1" + 13 * t), .n (val% «verify_tables» "zeta")]
    [.n (val% «verify_tables» "pad_weight[0]" + 13 * t), .n (val% «verify_tables» "lead@1" + 13 * t), .n (val% «verify_tables» "rest@1" + 13 * t)]

/-- The `plus_one_run` dispatch. -/
def porCall : Stmt := .dispatch (.n (val% «verify_tables» "g_bus_mu")) plusOneRunNames [.n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "zeta")] [.n (val% «verify_tables» "zeta1_done")]

/-- Table `t`'s `shared_selector_tables` call. -/
def shCall (t : ℕ) : Stmt :=
  .call "shared_selector_tables" [.n (vtEqV t), .n (vtGV t), .n (vtShZ t), .n (vtShZ t + 1),
    .n (vtShZ t + 2), .n (vtShLen t)] []

/-- Framework block `b`'s `block_selector` dispatch. -/
def fwCall (b : ℕ) : Stmt :=
  .dispatch (.n (vtFwW b)) vtBsNames [.n (vtFwW b + 7), .n (vtFwW b + 8), .n (vtFwW b + 9)]
    [.n (vtFwW b + 10), .n (vtFwW b + 11)]

/-- An `index_mle` dispatch on `g^κ` at `kv`. -/
def imCall (kv r : ℕ) : Stmt := .dispatch (.n kv) vtImNames [.n (val% «verify_tables» "zeta")] [.n r]

/-- A table block's `block_selector_tab` dispatch (`vtSelT`). -/
def selCall (x : ℕ × ℕ × ℕ × ℕ × Option ℕ) : Stmt :=
  .dispatch (.n (vtShLen x.2.2.2.1)) vtBstNames [.n x.2.2.1, .n (vtEqV x.2.2.2.1), .n (vtGV x.2.2.2.1)]
    [.n (vtSelE x.2.2.1 x.2.2.2.1), .n (vtSelE x.2.2.1 x.2.2.2.1 + 1)]

/-- The `verify_tables_loop0` call. -/
def loopCall : Stmt :=
  .callIf (.n (val% «verify_tables» "s73#1")) name% «verify_tables_loop0» [.n (val% «verify_tables» "s73#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"), .n (val% «verify_tables» "tabs"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zc_cprod")]

/-- The `eq_prefix_chain_rev` call. -/
def epcCall : Stmt := .call "eq_prefix_chain_rev" [.n (val% «verify_tables» "zc_peq"), .n (val% «verify_tables» "chi"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "g_zc_n")] []

/-- The slot sumcheck's tail round `k` (`k < 3`): its capacity, cursor and claim, `tabs`. -/
def otrCall (k : ℕ) : Stmt :=
  .call "opening_tail_round"
    ([[.n (val% «verify_tables» "nxt[8]@2"), .n (val% «verify_tables» "nxt[9]@2"), .n (val% «verify_tables» "nxt[10]@2"), .n (val% «verify_tables» "nxt[11]@2"), .n (val% «verify_tables» "nxt[12]@2"), .n (val% «verify_tables» "bfs0@1~9"), .n (val% «verify_tables» "bc_claim@1")],
      [.n (val% «verify_tables» "bfs0@1"), .n (val% «verify_tables» "bfs1@1"), .n (val% «verify_tables» "bfs2@1"), .n (val% «verify_tables» "bfs3@1"), .n (val% «verify_tables» "bfs4@1"), .n (val% «verify_tables» "cursor@2"), .n (val% «verify_tables» "bc_claim@2")],
      [.n (val% «verify_tables» "bfs0@2"), .n (val% «verify_tables» "bfs1@2"), .n (val% «verify_tables» "bfs2@2"), .n (val% «verify_tables» "bfs3@2"), .n (val% «verify_tables» "bfs4@2"), .n (val% «verify_tables» "cursor@3"), .n (val% «verify_tables» "bc_claim@3")]].getD k [] ++ [.n (val% «verify_tables» "tabs")])
    ((List.range 8).map fun i ↦ .n (val% «verify_tables» "bfs0@1" + 8 * k + i))

/-- `verify_tables`' calls, in order. -/
def vtCalls : List Stmt :=
  (List.range 6).map pwCall ⧺ [porCall] ⧺ (List.range 6).map shCall ⧺
    [fwCall 0, fwCall 1, imCall (val% «verify_tables» "kb[1]") (val% «verify_tables» "coord_val@1"), fwCall 2, imCall (val% «verify_tables» "kappa_g@2") (val% «verify_tables» "coord_val@2")] ⧺
    (List.range 51).map (fun i ↦ selCall (vtPushSel.getD i default)) ⧺
    (List.range 45).map (fun i ↦ selCall (vtCountSel.getD i default)) ⧺
    [otrCall 0, otrCall 1, otrCall 2, loopCall, epcCall]

set_option maxRecDepth 100000 in
/-- **The calls, by the kernel**: the statements that are not plain. -/
theorem vt_calls : stmtsEqb (vtPre.filter fun s ↦ !plainStB s) vtCalls = true := by
  decide +kernel

theorem vt_call_mem {s : Stmt} (hs : s ∈ vtPre) (hp : plainStB s = false) : s ∈ vtCalls := by
  rw [← stmtsEqb_sound vt_calls]
  exact List.mem_filter.mpr ⟨hs, by simp [hp]⟩

set_option maxRecDepth 100000 in
/-- The shared tables' pointers: `zeta`, `zeta1` and the exponent table at `g^τ`. -/
theorem vt_sh_muls : ∀ t < 6, stmtsEqb [.atom (.mul (.n (vtShZ t)) (.n (val% «verify_tables» "zeta")) (.n ((val% «verify_tables» "kb[2]") + t))),
    .atom (.mul (.n (vtShZ t + 1)) (.n (val% «verify_tables» "zeta1")) (.n ((val% «verify_tables» "kb[2]") + t))),
    .atom (.mul (.n (vtShZ t + 2)) (.n (val% «verify_tables» "g_squares")) (.n ((val% «verify_tables» "kb[2]") + t)))]
    ((vtPre.drop (vtShC t)).take 3) = true := by
  simp only [vtPre_drop]; decide +kernel

set_option maxRecDepth 100000 in
/-- A framework block's pointers. -/
theorem vt_fw_muls : ∀ b < 3, stmtsEqb (vtFwSelT (vtFwW b) b ([val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0)
    ([none, some (val% «verify_tables» "eq_hi@1"), some (val% «verify_tables» "selector_sum@1")].getD b none))
    ((vtPre.drop ([pos% «verify_tables» "s30.u0.s2.u0.s3.e.s2.e.s0#0", pos% «verify_tables» "s30.u0.s2.u1.s3.e.s2.e.s0#0", pos% «verify_tables» "s30.u0.s2.u2.s3.e.s2.e.s0#0"].getD b 0)).take
      (vtFwSelT (vtFwW b) b ([val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0) ([none, some (val% «verify_tables» "eq_hi@1"), some (val% «verify_tables» "selector_sum@1")].getD b none)).length)
    = true := by
  simp only [vtPre_drop]; decide +kernel

set_option maxRecDepth 100000 in
theorem vt_sel_shapes : (∀ i < 51, (vtPushSel.getD i default).2.2.2.1 < 6 ∧
      val% «verify_tables» "block_index_mle" < (vtPushSel.getD i default).2.2.1) ∧
    ∀ i < 45, (vtCountSel.getD i default).2.2.2.1 < 6 ∧
      val% «verify_tables» "block_index_mle" < (vtCountSel.getD i default).2.2.1 := by
  decide +kernel

/-! ## Regions -/

/-- The region of the caller's and the own buffers. -/
abbrev VtHonest.reg (H : VtHonest) (B : VtBases) : ℕ → Prop := RegionL (H.linL B ++ H.ownL B)

theorem allocVars_mem {j : ℕ} (hj : j < 122) : vtAllocVars.getD j 0 ∈ vtAllocVars := by
  rw [List.getD_eq_getElem _ _ (by rw [vtAllocVars_length]; exact hj)]
  exact List.getElem_mem _

theorem getD_length_map : ∀ (l : List (List E)) (j : ℕ),
    (l.getD j []).length = (l.map List.length).getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, j + 1 => by simpa using getD_length_map l j

theorem shSizes_length (H : VtHonest) : H.shSizes.length = 12 := by
  simp [VtHonest.shSizes]

/-- A list index bound, by the lists' lengths. -/
local macro "len_omega" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only
  [List.length_cons, List.length_nil, List.length_append, List.length_replicate, shSizes_length]; omega))

theorem sizes_digits (H : VtHonest) {j : ℕ} (h1 : 22 ≤ j) (h2 : j < 118) : H.sizes.getD j 0 = 9 := by
  unfold VtHonest.sizes
  rw [List.getD_append _ _ _ _ (by simp [shSizes_length]; omega),
    List.getD_append_right _ _ _ _ (by simp [shSizes_length]; omega),
    List.getD_eq_getElem _ _ (by simp [shSizes_length]; omega), List.getElem_replicate]

theorem sizes_bits (H : VtHonest) {b : ℕ} (hb : b < 3) : H.sizes.getD (19 + b) 0 = 34 := by
  unfold VtHonest.sizes
  simp only [List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by len_omega), List.getD_append_right _ _ _ _ (by len_omega),
    List.getD_append _ _ _ _ (by len_omega)]
  simp only [shSizes_length, List.length_cons, List.length_nil]
  interval_cases b <;> rfl

theorem sizes_Z (H : VtHonest) : H.sizes.getD 118 0 = 245 ∧ H.sizes.getD 119 0 = 35 ∧
    H.sizes.getD 120 0 = 34 ∧ H.sizes.getD 121 0 = 35 := by
  unfold VtHonest.sizes
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [List.getD_append_right _ _ _ _ (by simp [shSizes_length])] <;> simp [shSizes_length]

theorem sizes_sh (H : VtHonest) {t : ℕ} (ht : t < 6) :
    H.sizes.getD (4 + 2 * t) 0 = 8 * (H.μ - H.τ t + 1) ∧
      H.sizes.getD (5 + 2 * t) 0 = 4 * (H.μ - H.τ t + 1) := by
  have e : ∀ k < 12, H.sizes.getD (4 + k) 0 = H.shSizes.getD k 0 := by
    intro k hk
    unfold VtHonest.sizes
    simp only [List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by len_omega), List.getD_append _ _ _ _ (by len_omega)]
    simp
  rw [show 5 + 2 * t = 4 + (2 * t + 1) by omega, e _ (by omega), e _ (by omega)]
  simp only [VtHonest.shSizes]
  interval_cases t <;> exact ⟨rfl, rfl⟩

/-- **What `verify_tables`' placed calls need**: the shapes, the oracle, the memory, and what
`vt_rel_completeF` gives of `kappa_base` and the shared lengths. -/
structure VtIn (H : VtHonest) (B : VtBases) (w : ℕ → E) (rd : Reader) : Prop where
  ok : H.Ok
  hs : VtShape H
  hw : VtWOk H B w
  hm : MemLay rd (H.linL B ++ H.ownL B)
  kbsh : VtKbSh H (vtσ rd w (H.args B))

section
variable {H : VtHonest} {B : VtBases} {w : ℕ → E} {rd : Reader}

theorem ptr_lin {q : ℕ × List E} (hq : q ∈ H.linL B) {j n : ℕ} (h : j + n ≤ q.2.length) :
    PtrIn (H.reg B) (ofK (addressOfIndex q.1) * gen ^ j) n := by
  refine ptrIn_mul (ptrIn_ofK fun i hi ↦ ?_)
  unfold VtHonest.reg RegionL
  exact ⟨q, List.mem_append_left _ hq, by omega, by omega⟩

theorem ptr_lin0 {q : ℕ × List E} (hq : q ∈ H.linL B) {n : ℕ} (h : n ≤ q.2.length) :
    PtrIn (H.reg B) (ofK (addressOfIndex q.1)) n := by
  simpa using ptr_lin hq (j := 0) (n := n) (by omega)

theorem ptr_own (hw : VtWOk H B w) {j v : ℕ} (hj : j < 122) (hv : vtAllocVars.getD j 0 = v)
    {a n : ℕ} (h : a + n ≤ H.sizes.getD j 0) : PtrIn (H.reg B) (w v * gen ^ a) n := by
  subst hv
  rw [hw.alloc j hj]
  have hb := ownB_length H B
  have ho := ownW_length H B
  have hmem : ((H.ownB B).getD j 0, (H.ownW B).getD j []) ∈ H.ownL B := by
    rw [VtHonest.ownL, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨j, by simp [hb, ho]; omega, by simp⟩
  have hl : ((H.ownW B).getD j []).length = H.sizes.getD j 0 := by
    rw [getD_length_map, ownW_lengths]
  refine ptrIn_mul (ptrIn_ofK fun i hi ↦ ?_)
  unfold VtHonest.reg RegionL
  exact ⟨_, List.mem_append_right _ hmem, by simp, by simp only; omega⟩

theorem ptr_own0 (hw : VtWOk H B w) {j v : ℕ} (hj : j < 122) (hv : vtAllocVars.getD j 0 = v)
    {n : ℕ} (h : n ≤ H.sizes.getD j 0) : PtrIn (H.reg B) (w v) n := by
  simpa using ptr_own hw hj hv (a := 0) (n := n) (by omega)

/-! ## The valuation's values -/

local notation "σv" => vtσ rd w (H.args B)

theorem vt_p {i : ℕ} (hi : i < 21) : σv (.n i) = (H.args B).getD i 0 := vt_param rfl hi

theorem vt_s8 : σv (.n (val% «verify_tables» "zeta")) = ofK (addressOfIndex B.zeta) := vt_p (by norm_num)

theorem vt_s9 : σv (.n (val% «verify_tables» "g_bus_mu")) = gen ^ H.μ := vt_p (by norm_num)

theorem vt_s12 : σv (.n (val% «verify_tables» "g_squares")) = ofK (addressOfIndex B.sq) := vt_p (by norm_num)

theorem vt_s16 : σv (.n (val% «verify_tables» "chi")) = ofK (addressOfIndex B.chi) := vt_p (by norm_num)

theorem vt_alloc' {v : ℕ} (hv : v ∈ vtAllocVars) : σv (.n v) = w v := vt_alloc_var rfl hv

theorem vt_const {d : ℕ} {e : E} (hs : Stmt.atom (.const (.n d) e) ∈ vtPre) : σv (.n d) = e :=
  vt_goodS rfl hs

theorem vt_add {d x y : ℕ} (hs : Stmt.atom (.add (.n d) (.n x) (.n y)) ∈ vtPre) :
    σv (.n d) = σv (.n x) + σv (.n y) :=
  vt_goodS rfl hs

theorem vt_mulF {d x y : ℕ} (hs : Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ vtPre) (h1 : x < d)
    (h2 : y < d) : σv (.n d) = σv (.n x) * σv (.n y) := by
  have g : GoodS rd vtSL w σv (fixNe (.atom (.mul (.n d) (.n x) (.n y)))) := vt_goodS rfl hs
  simp only [fixNe, GoodS, Good] at g
  rwa [ite_pos' (show (V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx from ⟨h1, h2⟩)] at g

theorem vt_mulB {d x y : ℕ} (hs : Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ vtPre) (h : d < x) :
    σv (.n x) = σv (.n d) * (σv (.n y))⁻¹ := by
  have g : GoodS rd vtSL w σv (fixNe (.atom (.mul (.n d) (.n x) (.n y)))) := vt_goodS rfl hs
  simp only [fixNe, GoodS, Good] at g
  rwa [ite_neg' (show ¬((V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx) from
    fun h' ↦ absurd h'.1 (by show ¬x < d; omega))] at g

theorem gen_div {a b : ℕ} (h : b ≤ a) : gen ^ a * (gen ^ b)⁻¹ = gen ^ (a - b) :=
  (pow_sub₀ _ gen_ne_zero h).symm

theorem vt_kbt (I : VtIn H B w rd) {t : ℕ} (ht : t < 6) : σv (.n (val% «verify_tables» "kb[2]" + t)) = gen ^ H.τ t := by
  have := I.kbsh.1 (2 + t) (by omega)
  rw [show 26 + (2 + t) = 28 + t by omega, show 2 + t = t + 1 + 1 by omega] at this
  rw [this]
  simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
  rw [vtTauList_getD ht]

theorem vt_kb0 (I : VtIn H B w rd) : σv (.n (val% «verify_tables» "kb[0]")) = 1 := by simpa using I.kbsh.1 0 (by norm_num)

theorem vt_kb1 (I : VtIn H B w rd) : σv (.n (val% «verify_tables» "kb[1]")) = gen ^ H.lm := by
  simpa using I.kbsh.1 1 (by norm_num)

theorem vt_nμ (I : VtIn H B w rd) : H.n ≤ H.μ := by
  obtain ⟨t, ht, e⟩ := vt_n_ex I.hs.hr
  rw [← e]; exact I.hs.hτμ t ht

theorem vt_e2500 (I : VtIn H B w rd) : σv (.n (val% «verify_tables» "g_zc_n")) = gen ^ H.n := by
  have g : GoodS rd vtSL w σv
      (fixNe (.atom (.hint (.witness "zc_tau_max" (.stack [.n (val% «verify_tables» "g_zc_n")]))))) :=
    vt_goodS rfl (vt_mem_at (pos% «verify_tables» "g_zc_n") _ (by decide +kernel))
  have := g (.n (val% «verify_tables» "g_zc_n")) (by simp)
  rw [this]; exact I.hw.w2544

/-! ## Each family -/

theorem vt_pw_up (I : VtIn H B w rd) {t : ℕ} (ht : t < 6)
    (h : VSH (coreProgram.Rel rd) rd σv (pwCall t)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (pwCall t) := by
  have h31 : H.τ t < 31 := I.hs.hτ31 t ht
  have hl : vtPadNames.length = 31 := by simp [vtPadNames]
  refine vsh_disp (vt_kbt I ht) (by rw [hl]; exact h31) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtPadNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hc ⊢
  refine padding_weight_relIn h31 ?_ hc
  rw [vt_s8]
  exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) (I.hs.hτμ t ht)

theorem vt_por_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv porCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv porCall := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hl : plusOneRunNames.length = 34 := rfl
  have hm' : H.μ < plusOneRunNames.length := by rw [hl]; omega
  have e703 : σv (.n (val% «verify_tables» "zeta1")) = w 802 := vt_alloc' (by unfold vtAllocVars; simp)
  refine vsh_disp vt_s9 hm' (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [List.map_cons, List.map_nil] at hc ⊢
  rw [← List.getD_eq_getElem _ "" hm'] at hc ⊢
  refine plus_one_run_relIn (by omega) ?_ ?_ hc
  · rw [e703]
    exact ptr_own0 I.hw (j := 16 + 1) (by norm_num) rfl (le_of_eq rfl)
  · rw [vt_s8]
    exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) le_rfl

/-- Table `t`'s shared tables' pointers: the oracle's allocations. -/
theorem vt_shptr {t : ℕ} (ht : t < 6) :
    σv (.n (vtEqV t)) = w (vtShV t + 11) ∧ σv (.n (vtGV t)) = w (vtShV t + 15) := by
  obtain ⟨-, eE, eG⟩ := vtSh_vals t ht
  have hm : ∀ s ∈ vtShAT t, s ∈ vtPre := fun s hs ↦
    vt_mem_slice (n := vtShA t) (by rw [vtPre_drop]; exact vtShAT_check t ht) hs
  have c1 : σv (.n (vtShV t + 12)) = σv (.n (vtShV t + 11)) :=
    vt_goodS rfl (hm (.atom (.copy (.n (vtShV t + 12)) (.n (vtShV t + 11)))) (by simp [vtShAT]))
  have c2 : σv (.n (vtShV t + 16)) = σv (.n (vtShV t + 15)) :=
    vt_goodS rfl (hm (.atom (.copy (.n (vtShV t + 16)) (.n (vtShV t + 15)))) (by simp [vtShAT]))
  have a1 : vtShV t + 11 ∈ vtAllocVars := (vtAllocVars_Sh t ht).1 ▸ allocVars_mem (by omega)
  have a2 : vtShV t + 15 ∈ vtAllocVars := (vtAllocVars_Sh t ht).2 ▸ allocVars_mem (by omega)
  rw [eE, eG, c1, c2, vt_alloc' a1, vt_alloc' a2]
  exact ⟨rfl, rfl⟩

theorem vt_sh_up (I : VtIn H B w rd) {t : ℕ} (ht : t < 6)
    (h : VSH (coreProgram.Rel rd) rd σv (shCall t)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (shCall t) := by
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  have hμ : H.μ < 33 := I.hs.hμ33
  have hlen := I.kbsh.2 t ht
  have e703 : σv (.n (val% «verify_tables» "zeta1")) = w 802 := vt_alloc' (by unfold vtAllocVars; simp)
  obtain ⟨ep, eg⟩ := vt_shptr (H := H) (B := B) (w := w) (rd := rd) ht
  have hz0 : 804 ≤ vtShZ t := by unfold vtShZ; omega
  have mem : ∀ s ∈ [Stmt.atom (.mul (.n (vtShZ t)) (.n (val% «verify_tables» "zeta")) (.n (val% «verify_tables» "kb[2]" + t))),
      .atom (.mul (.n (vtShZ t + 1)) (.n (val% «verify_tables» "zeta1")) (.n (val% «verify_tables» "kb[2]" + t))),
      .atom (.mul (.n (vtShZ t + 2)) (.n (val% «verify_tables» "g_squares")) (.n (val% «verify_tables» "kb[2]" + t)))], s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vt_sh_muls t ht) hs
  have ez := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (vtShZ t)) (.n (val% «verify_tables» "zeta")) (.n (val% «verify_tables» "kb[2]" + t)))) (by simp)) (by omega) (by omega)
  have ez1 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (vtShZ t + 1)) (.n (val% «verify_tables» "zeta1")) (.n (val% «verify_tables» "kb[2]" + t)))) (by simp)) (by omega) (by omega)
  have egs := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (vtShZ t + 2)) (.n (val% «verify_tables» "g_squares")) (.n (val% «verify_tables» "kb[2]" + t)))) (by simp)) (by omega) (by omega)
  have kb := vt_kbt I ht
  obtain ⟨sE, sG⟩ := sizes_sh H ht
  simp only [shCall, vsh_call, List.map_cons, List.map_nil] at h ⊢
  rw [hlen] at h ⊢
  refine shared_selector_tables_relIn (by omega) ?_ ?_ ?_ ?_ ?_ h
  · rw [ep]
    exact ptr_own0 I.hw (j := 4 + 2 * t) (by omega) (vtAllocVars_Sh t ht).1 (by rw [sE]; omega)
  · rw [eg]
    exact ptr_own0 I.hw (j := 5 + 2 * t) (by omega) (vtAllocVars_Sh t ht).2 (by rw [sG]; omega)
  · rw [ez, kb, vt_s8]
    exact ptr_lin (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) (by
      show H.τ t + (H.μ - H.τ t) ≤ H.μ; omega)
  · rw [ez1, kb, e703]
    exact ptr_own I.hw (j := 16 + 1) (by norm_num) rfl (by
      show H.τ t + (H.μ - H.τ t) ≤ H.μ; omega)
  · rw [egs, kb, vt_s12]
    exact ptr_lin (q := (B.sq, expTableWordsW)) (by simp [VtHonest.linL]) (by
      rw [length_expTableWordsW, show (2 : ℕ) ^ winTabBits = 2048 from rfl]; omega)

theorem vt_fw_kv (I : VtIn H B w rd) {b : ℕ} (hb : b < 3) :
    σv (.n ([val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0)) = gen ^ ([0, H.lm, 19].getD b 0) := by
  interval_cases b
  · show σv (.n (val% «verify_tables» "kb[0]")) = gen ^ 0
    rw [vt_kb0 I, pow_zero]
  · exact vt_kb1 I
  · show σv (.n (val% «verify_tables» "kappa_g@2")) = gen ^ 19
    rw [vt_mulF (H := H) (B := B) (w := w) (rd := rd) (d := 866) (x := 26) (y := 865)
        (vt_mem_at 854 _ (by decide +kernel)) (by norm_num) (by norm_num),
      vt_const (H := H) (B := B) (w := w) (rd := rd) (d := 865) (e := word 524288 0)
        (vt_mem_at 853 _ (by decide +kernel)), show (524288 : ℕ) = 2 ^ 19 by norm_num,
      word_two_pow (by norm_num), vt_kb0 I, one_mul]

theorem vt_fw_up (I : VtIn H B w rd) {b : ℕ} (hb : b < 3)
    (h : VSH (coreProgram.Rel rd) rd σv (fwCall b)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (fwCall b) := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hκ : [0, H.lm, 19].getD b 0 ≤ H.μ := by
    have h1 : H.lm ≤ H.μ := I.hs.hlmμ
    have h2 : 19 ≤ H.μ := I.hs.h19
    interval_cases b <;> simp <;> omega
  have hwv : [val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0 < vtFwW b ∧ 810 < vtFwW b := by
    interval_cases b <;> simp [vtFwW]
  set κ := [0, H.lm, 19].getD b 0 with hκd
  set kv := [val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0 with hkv
  set v := vtFwW b with hv
  have mem : ∀ s ∈ vtFwSelT v b kv ([none, some (val% «verify_tables» "eq_hi@1"), some (val% «verify_tables» "selector_sum@1")].getD b none), s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vt_fw_muls b hb) hs
  have e0 : σv (.n kv) = gen ^ κ := vt_fw_kv I hb
  have ew : σv (.n v) = gen ^ (H.μ - κ) := by
    rw [vt_mulB (mem (.atom (.mul (.n (val% «verify_tables» "g_bus_mu")) (.n v) (.n kv))) (by simp [vtFwSelT])) (by omega),
      vt_s9, e0, gen_div hκ]
  have e7 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 7)) (.n (v + 6)) (.n kv))) (by simp [vtFwSelT])) (by omega)
    (by omega)
  have e8 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 8)) (.n (val% «verify_tables» "zeta1")) (.n kv))) (by simp [vtFwSelT])) (by omega) (by omega)
  have e9 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 9)) (.n (val% «verify_tables» "idxc_tab")) (.n kv))) (by simp [vtFwSelT])) (by omega) (by omega)
  have hjv : vtAllocVars.getD (19 + b) 0 = v + 6 := vtAllocVars_F b hb
  have a6 : σv (.n (v + 6)) = w (v + 6) := by
    rw [← hjv]; exact vt_alloc' (allocVars_mem (by omega))
  have a703 : σv (.n (val% «verify_tables» "zeta1")) = w 802 := vt_alloc' (by unfold vtAllocVars; simp)
  have a668 : σv (.n (val% «verify_tables» "idxc_tab")) = w 767 := vt_alloc' (by unfold vtAllocVars; simp)
  have hl : vtBsNames.length = 34 := by simp [vtBsNames]
  refine vsh_disp ew (by rw [hl]; omega) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtBsNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine block_selector_relIn (by omega) ?_ ?_ ?_ hc
  · rw [e7, a6, e0]
    exact ptr_own I.hw (j := 19 + b) (by omega) hjv (by rw [sizes_bits H hb]; omega)
  · rw [e8, a703, e0]
    exact ptr_own I.hw (j := 16 + 1) (by norm_num) rfl (by
      show κ + (H.μ - κ) ≤ H.μ; omega)
  · rw [e9, a668, e0]
    exact ptr_own I.hw (j := 16 + 0) (by norm_num) rfl (by
      show κ + (H.μ - κ) ≤ 34; omega)

theorem vt_im_up (I : VtIn H B w rd) {b r : ℕ} (hb : b = 1 ∨ b = 2)
    (h : VSH (coreProgram.Rel rd) rd σv (imCall ([val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0) r)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (imCall ([val% «verify_tables» "kb[0]", val% «verify_tables» "kb[1]", val% «verify_tables» "kappa_g@2"].getD b 0) r) := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hκ : [0, H.lm, 19].getD b 0 ≤ H.μ := by
    have h1 : H.lm ≤ H.μ := I.hs.hlmμ
    have h2 : 19 ≤ H.μ := I.hs.h19
    rcases hb with rfl | rfl <;> simp <;> omega
  have hl : vtImNames.length = 34 := by simp [vtImNames]
  refine vsh_disp (vt_fw_kv I (by omega)) (by rw [hl]; omega) (by rw [hl]; norm_num)
    (fun hc ↦ ?_) h
  simp only [vtImNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine index_mle_relIn (by omega) ?_ hc
  rw [vt_s8]
  exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) hκ

/-- **`block_selector_tab`'s digits**: nibbles of the offset above `τ`. -/
theorem vt_digits {sb : E} {off τ n : ℕ} (hob : off < 2 ^ (τ + n)) (hn : n ≤ 36)
    (h : ReadsAt rd sb (offDigits off τ)) :
    ∀ k < btN n, ∃ u < 2 ^ btW n k, LoadHolds rd sb k (gen ^ u) := by
  intro k hk
  have hr := offDigits_reads hn hob h
  have hbl : (selBitsOf off τ n).length = n := selBitsOf_length _ _ _
  have hlen : k < (nibDigits (selBitsOf off τ n)).length := by
    simp only [nibDigits, List.length_map, List.length_range, hbl]; exact hk
  refine ⟨btkU n (selBitsOf off τ n) k, btkU_lt _ _ _, ?_⟩
  have := hr k hlen
  rwa [← List.getD_eq_getElem _ 0 hlen, btk_digit hbl hk] at this

theorem vt_sel_up (I : VtIn H B w rd) {x : ℕ × ℕ × ℕ × ℕ × Option ℕ}
    (hchk : stmtsEqb (vtSelT x.2.2.1 x.1 x.2.2.2.1 x.2.2.2.2)
      ((vtAt x.2.1).take (vtSelT x.2.2.1 x.1 x.2.2.2.1 x.2.2.2.2).length) = true)
    (ht : x.2.2.2.1 < 6) (hw0 : val% «verify_tables» "block_index_mle" < x.2.2.1)
    {j : ℕ} (hj1 : 22 ≤ j) (hj : j < 118) (hjv : vtAllocVars.getD j 0 = x.2.2.1) {off : ℕ}
    (hob : off < 2 ^ H.μ)
    (hdig : ReadsAt rd (w x.2.2.1) (offDigits off (H.τ x.2.2.2.1)))
    (h : VSH (coreProgram.Rel rd) rd σv (selCall x)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (selCall x) := by
  obtain ⟨b, pos, v, t, prev⟩ := x
  simp only at hchk ht hw0 hjv hdig
  have hμ : H.μ < 33 := I.hs.hμ33
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  have av : σv (.n v) = w v := by
    rw [← hjv]; exact vt_alloc' (allocVars_mem (by omega))
  obtain ⟨ep, eg⟩ := vt_shptr (H := H) (B := B) (w := w) (rd := rd) ht
  obtain ⟨sE, sG⟩ := sizes_sh H ht
  have hl : vtBstNames.length = 34 := by simp [vtBstNames]
  refine vsh_disp (I.kbsh.2 t ht) (by rw [hl]; omega) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtBstNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine block_selector_tab_relIn (by omega) ?_ ?_ ?_ ?_ hc
  · rw [av]
    exact ptr_own0 I.hw (by omega) hjv (by
      rw [sizes_digits H hj1 hj]; simp only [btN]; omega)
  · rw [av]
    exact vt_digits (by rw [show H.τ t + (H.μ - H.τ t) = H.μ by omega]; exact hob) (by omega)
      hdig
  · rw [ep]
    exact ptr_own0 I.hw (j := 4 + 2 * t) (by omega) (vtAllocVars_Sh t ht).1 (by rw [sE]; omega)
  · rw [eg]
    exact ptr_own0 I.hw (j := 5 + 2 * t) (by omega) (vtAllocVars_Sh t ht).2 (by rw [sG]; omega)

theorem vt_loop_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv loopCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv loopCall := by
  unfold loopCall at h ⊢
  refine ⟨h.1, fun hne ↦ ?_⟩
  have hc := h.2 hne
  have e2500 := vt_e2500 I
  have e2597 : σv (.n (val% «verify_tables» "s73#1")) = 1 + gen ^ H.n := by
    rw [vt_add (d := 2323) (x := 2322) (y := 2240) (vt_mem_at 2352 _ (by decide +kernel)),
      vt_const (vt_mem_at 2351 (.atom (.const (.n (val% «verify_tables» "s73#0")) (word 1 0))) (by decide +kernel)),
      word_one, e2500]
  have e2598 : σv (.n (val% «verify_tables» "s73#2")) = gen ^ 0 := by
    rw [vt_const (vt_mem_at 2353 (.atom (.const (.n (val% «verify_tables» "s73#2")) (word 1 0))) (by decide +kernel)),
      word_one, pow_zero]
  have hK : 0 < H.n := by
    rcases Nat.eq_zero_or_pos H.n with h0 | h0
    · exact absurd (by rw [e2597, h0, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
    · exact h0
  have a2589 : σv (.n (val% «verify_tables» "zc_rounds")) = w 2316 := vt_alloc' (by unfold vtAllocVars; simp)
  have a2592 : σv (.n (val% «verify_tables» "zc_cprod")) = w 2317 := vt_alloc' (by unfold vtAllocVars; simp)
  have a2635 : σv (.n (val% «verify_tables» "zc_rk")) = w 2321 := vt_alloc' (by unfold vtAllocVars; simp)
  simp only [List.map_cons, List.map_nil] at hc ⊢
  rw [e2598, e2500, a2589, a2592, a2635] at hc ⊢
  obtain ⟨d, hd⟩ := hc
  -- the rounds' cursor words
  have hR : ReadsAt rd (w 2316)
      (zcRoundsW H.cap0 H.target (ofK (addressOfIndex B.cur) * gen ^ 13 * gen) H.xsR H.n) := by
    have := vt_own_reads I.hm I.hw (j := 118 + 0) (by norm_num)
    rw [ownW_getD_Z H B (k := 0) (by norm_num), show vtAllocVars.getD (118 + 0) 0 = 2316 by decide]
      at this
    simp only [List.getD_cons_zero] at this
    have hn := vt_nμ I
    have hμ : H.μ < 33 := I.hs.hμ33
    exact tbReads_unpad this (by rw [zcRoundsW_len (cap0_length H)]; omega)
  have hcur : ∀ k < H.n, ∀ c, LoadHolds rd (w 2316 * gen ^ (7 * k)) 5 c →
      PtrIn (H.reg B) c 3 := by
    intro k hk c hcl
    have r := zcRoundsW_reads (cap0_length H) hR k hk.le
    have hl5 := cap0_length H
    have l5 := tb_load_of r (k := 5) (by simp [zcRecW_len hl5])
    rw [zcRecW, List.getD_append_right _ _ _ _ (by simp [zcRec_len hl5]), zcRec_len hl5] at l5
    have e : c = ofK (addressOfIndex B.cur) * gen ^ (14 + 3 * k) := by
      rw [Option.some.inj (hcl.2.symm.trans l5.2)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      ring
    rw [e]
    have hcl' : 14 + 3 * k + 3 ≤ H.curW.length := by
      simp only [VtHonest.curW, List.length_append, I.ok.hx4, I.ok.hbcW, I.ok.hxR]; omega
    exact ptr_lin (q := (B.cur, H.curW)) (by simp [VtHonest.linL]) hcl'
  have hn33 := vt_nμ I
  have hμ33 : H.μ < 33 := I.hs.hμ33
  refine loop10_relIn ?_ ?_ ?_ hcur d 0 hK hd
  · exact ptr_own0 I.hw (j := 118) (by norm_num) (by decide) (by rw [(sizes_Z H).1]; omega)
  · exact ptr_own0 I.hw (j := 120) (by norm_num) (by decide) (by rw [(sizes_Z H).2.2.1]; omega)
  · exact ptr_own0 I.hw (j := 119) (by norm_num) (by decide) (by rw [(sizes_Z H).2.1]; omega)

theorem vt_epc_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv epcCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv epcCall := by
  have e2500 := vt_e2500 I
  have a2613 : σv (.n (val% «verify_tables» "zc_peq")) = w 2337 := vt_alloc' (by unfold vtAllocVars; simp)
  have a2635 : σv (.n (val% «verify_tables» "zc_rk")) = w 2321 := vt_alloc' (by unfold vtAllocVars; simp)
  have a703 : σv (.n (val% «verify_tables» "zeta1")) = w 802 := vt_alloc' (by unfold vtAllocVars; simp)
  have hnμ := vt_nμ I
  have hμ : H.μ < 33 := I.hs.hμ33
  simp only [epcCall, vsh_call, List.map_cons, List.map_nil] at h ⊢
  rw [e2500] at h ⊢
  refine eq_prefix_chain_rev_relIn (by omega) ?_ ?_ ?_ ?_ h
  · rw [a2613]; exact ptr_own0 I.hw (j := 121) (by norm_num) (by decide) (by rw [(sizes_Z H).2.2.2]; omega)
  · rw [vt_s16]
    exact ptr_lin0 (q := (B.chi, H.chiW)) (by simp [VtHonest.linL]) (by
      simp [VtHonest.chiW, zcChis, zcRkW])
  · rw [a2635]
    exact ptr_own0 I.hw (j := 120) (by norm_num) (by decide) (by rw [(sizes_Z H).2.2.1]; omega)
  · rw [a703]; exact ptr_own0 I.hw (j := 16 + 1) (by norm_num) (by decide) hnμ

/-- The tail rounds' cursors: `7 + 2k` words into the stream. -/
theorem vt_otr_cursor (I : VtIn H B w rd) {k : ℕ} (hk : k < 3) :
    σv (.n ([1571, 1577, 1585].getD k 0)) = ofK (addressOfIndex B.cur) * gen ^ (7 + 2 * k) := by
  interval_cases k
  · show σv (.n (val% «verify_tables» "bfs0@1~9")) = _
    rw [vt_mulF (H := H) (B := B) (w := w) (rd := rd) (d := 1571) (x := 5) (y := 1570)
        (vt_mem_at 1634 _ (by decide +kernel)) (by norm_num) (by norm_num),
      vt_const (H := H) (B := B) (w := w) (rd := rd) (d := 1570) (e := word 128 0)
        (vt_mem_at 1633 _ (by decide +kernel)), show (128 : ℕ) = 2 ^ 7 by norm_num,
      word_two_pow (by norm_num), vt_p (by norm_num)]
    rfl
  · show σv (.n (val% «verify_tables» "cursor@2")) = _
    have g : GoodS rd vtSL w σv (otrCall 0) := vt_goodS rfl (vt_mem_at 1635 (otrCall 0) (by decide +kernel))
    have e := g (.n (val% «verify_tables» "cursor@2")) (List.mem_map.mpr ⟨5, List.mem_range.mpr (by norm_num), rfl⟩)
    have h1 := congrArg (fun l ↦ l.getD 5 0) I.hw.hw1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
      show (5 : ℕ) < 8 from by norm_num, Option.map_some, Option.getD_some] at h1
    rw [e, show (V.n (val% «verify_tables» "cursor@2")).idx = 1572 + 5 from rfl, h1, List.getElem?_append_right
      (by simp [vtBcR1, bcRound, Fs.squeeze, capOf])]
    simp only [List.length_cons, List.length_nil, vtBcR1, bcRound, Fs.squeeze, capOf]
    show (H.args B).getD 5 0 * gen ^ 7 * gen ^ 2 = _
    show ofK (addressOfIndex B.cur) * gen ^ 7 * gen ^ 2 = _
    ring
  · show σv (.n (val% «verify_tables» "cursor@3")) = _
    have g : GoodS rd vtSL w σv (otrCall 1) := vt_goodS rfl (vt_mem_at 1637 (otrCall 1) (by decide +kernel))
    have e := g (.n (val% «verify_tables» "cursor@3")) (List.mem_map.mpr ⟨5, List.mem_range.mpr (by norm_num), rfl⟩)
    have h1 := congrArg (fun l ↦ l.getD 5 0) I.hw.hw2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
      show (5 : ℕ) < 8 from by norm_num, Option.map_some, Option.getD_some] at h1
    rw [e, show (V.n (val% «verify_tables» "cursor@3")).idx = 1580 + 5 from rfl, h1, List.getElem?_append_right
      (by simp [vtBcR2, bcRound, Fs.squeeze, capOf])]
    simp only [List.length_cons, List.length_nil, vtBcR2, bcRound, Fs.squeeze, capOf]
    show ofK (addressOfIndex B.cur) * gen ^ 7 * gen ^ 2 * gen ^ 2 = _
    ring

theorem vt_otr_up (I : VtIn H B w rd) {k : ℕ} (hk : k < 3)
    (h : VSH (coreProgram.Rel rd) rd σv (otrCall k)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (otrCall k) := by
  have hc := vt_otr_cursor I hk
  have hlen : 7 + 2 * k + 2 ≤ H.curW.length := by
    simp only [VtHonest.curW, List.length_append, I.ok.hx4, I.ok.hbcW]; omega
  have hp := ptr_lin (H := H) (B := B) (q := (B.cur, H.curW)) (by simp [VtHonest.linL]) hlen
  interval_cases k
  all_goals
    simp only [otrCall, vsh_call, List.getD_cons_zero, List.getD_cons_succ, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil] at h ⊢
    refine opening_tail_round_relIn ?_ h
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hc
    rw [hc]
    exact hp

end

/-! ## Every statement -/

/-- **`verify_tables` is complete at the `RelIn` level**: under `vt_rel_complete`'s hypotheses,
every statement holds with its calls by relations loading from the caller's and the own buffers
only. -/
theorem vt_relIn_complete {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases) {w : ℕ → E}
    (hw : VtWOk H B w) {rd : Reader} (hlow : LowDefB 14 rd)
    (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    ∀ s ∈ vtPre, VSH (coreProgram.RelIn rd (RegionL (H.linL B ++ H.ownL B))) rd
      (vtσ rd w (H.args B)) s := by
  obtain ⟨⟨hV, -⟩, hks⟩ := vt_rel_completeF h hs B hw hlow hm
  have I : VtIn H B w rd := ⟨h, hs, hw, hm, hks⟩
  have hfitP := hs.hfitP
  have hfitC := hs.hfitC
  intro s hs'
  have hv := hV s hs'
  cases hp : plainStB s
  · have hc := vt_call_mem hs' hp
    simp only [vtCalls, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    obtain ⟨hP, hC⟩ := vt_sel_shapes
    rcases hc with (((((⟨t, ht, rfl⟩ | rfl) | ⟨t, ht, rfl⟩) | (rfl | rfl | rfl | rfl | rfl)) |
      ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
    · exact vt_pw_up I ht hv
    · exact vt_por_up I hv
    · exact vt_sh_up I ht hv
    · exact vt_fw_up I (b := 0) (by norm_num) hv
    · exact vt_fw_up I (b := 1) (by norm_num) hv
    · exact vt_im_up I (b := 1) (Or.inl rfl) hv
    · exact vt_fw_up I (b := 2) (by norm_num) hv
    · exact vt_im_up I (b := 2) (Or.inr rfl) hv
    · refine vt_sel_up I (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
        (hP i hi).1 (hP i hi).2 (j := 22 + i) (by omega)
        (by omega) (vtAllocVars_P i hi)
        (off := H.offP.getD (3 + i) 0)
        (vtB_stack_lt (vtSizesP H.lm (vtHt H.rows)) (b := 3 + i) (by rw [vtSizesP_length]; omega)
          hfitP) ?_ hv
      exact vt_own_reads' hm hw (j := 22 + i) (by omega) (vtAllocVars_P i hi)
        (ownW_getD_P H B hi)
    · refine vt_sel_up I (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
        (hC i hi).1 (hC i hi).2 (j := 73 + i) (by omega)
        (by omega) (vtAllocVars_C i hi)
        (off := H.offC.getD i 0)
        (vtB_stack_lt (vtSizesC (vtHt H.rows)) (b := i) (by rw [vtSizesC_length]; omega)
          hfitC) ?_ hv
      exact vt_own_reads' hm hw (j := 73 + i) (by omega) (vtAllocVars_C i hi)
        (ownW_getD_C H B hi)
    · exact vt_otr_up I (k := 0) (by norm_num) hv
    · exact vt_otr_up I (k := 1) (by norm_num) hv
    · exact vt_otr_up I (k := 2) (by norm_num) hv
    · exact vt_loop_up I hv
    · exact vt_epc_up I hv
  · exact vsh_plain hp hv

end
end LeanVM.Guest.B1.Tables
