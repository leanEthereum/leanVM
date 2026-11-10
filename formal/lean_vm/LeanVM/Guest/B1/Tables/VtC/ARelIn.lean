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

/-!
# The calls, placed

`plainStB`: an atom, or an `ite` of atoms, whose `VSH` does not depend on the call relation
(`vsh_plain`). `verify_tables`' other statements are its `119` calls (`vt_calls`, by the kernel):
the padding weights (`pwCall`), `plus_one_run` (`porCall`), the shared selector tables (`shCall`),
the framework blocks' selectors and `index_mle` (`fwCall`, `imCall`), the table blocks' selectors
on their hinted digits (`selCall`), the slot sumcheck's tail rounds (`otrCall`), `__loop9` and
`eq_prefix_chain`.

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
  .dispatch (.n (27 + t)) vtPadNames [.n (582 + 13 * t), .n 8]
    [.n (583 + 13 * t), .n (584 + 13 * t), .n (585 + 13 * t)]

/-- The `plus_one_run` dispatch. -/
def porCall : Stmt := .dispatch (.n 9) plusOneRunNames [.n 699, .n 8] [.n 700]

/-- Table `t`'s `shared_selector_tables` call. -/
def shCall (t : ℕ) : Stmt :=
  .call "shared_selector_tables" [.n (vtEqV t), .n (vtGV t), .n (709 + 13 * t), .n (710 + 13 * t),
    .n (711 + 13 * t), .n (vtShLen t)] []

/-- Framework block `b`'s `block_selector` dispatch. -/
def fwCall (b : ℕ) : Stmt :=
  .dispatch (.n (vtFwW b)) vtBsNames [.n (vtFwW b + 7), .n (vtFwW b + 8), .n (vtFwW b + 9)]
    [.n (vtFwW b + 10), .n (vtFwW b + 11)]

/-- An `index_mle` dispatch on `g^κ` at `kv`. -/
def imCall (kv r : ℕ) : Stmt := .dispatch (.n kv) vtImNames [.n 8] [.n r]

/-- A table block's `block_selector_tab` dispatch (`vtSelT`). -/
def selCall (x : ℕ × ℕ × ℕ × ℕ × Option ℕ × ℕ × ℕ × ℕ) : Stmt :=
  .dispatch (.n (vtShLen x.2.2.2.1)) vtBstNames [.n x.2.2.1,
      .n (if x.2.2.2.1 = 0 then 701 else x.2.2.1 + 2),
      .n (if x.2.2.2.1 = 0 then 702 else x.2.2.1 + 4)]
    [.n (vtSelE x.2.2.1 x.2.2.2.1), .n (vtSelE x.2.2.1 x.2.2.2.1 + 1)]

/-- The `__loop9` call. -/
def loopCall : Stmt :=
  .callIf (.n 2635) "__loop9" [.n 2636, .n 2544, .n 2627, .n 18, .n 16, .n 2544, .n 2630]

/-- The `eq_prefix_chain` call. -/
def epcCall : Stmt := .call "eq_prefix_chain" [.n 2651, .n 2652, .n 16, .n 699, .n 2544] []

/-- The slot sumcheck's tail round `k` (`k < 3`): its capacity, cursor and claim, `tabs`. -/
def otrCall (k : ℕ) : Stmt :=
  .call "opening_tail_round"
    ([[.n 1862, .n 1863, .n 1864, .n 1865, .n 1866, .n 1875, .n 1873],
      [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882],
      [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890]].getD k [] ++ [.n 18])
    ((List.range 8).map fun i ↦ .n (1876 + 8 * k + i))

/-- `verify_tables`' calls, in order. -/
def vtCalls : List Stmt :=
  (List.range 6).map pwCall ++ [porCall] ++ (List.range 6).map shCall ++
    [fwCall 0, fwCall 1, imCall 26 809, fwCall 2, imCall 821 837] ++
    (List.range 51).map (fun i ↦ selCall (vtPushSel.getD i default)) ++
    (List.range 45).map (fun i ↦ selCall (vtCountSel.getD i default)) ++
    [otrCall 0, otrCall 1, otrCall 2, loopCall, epcCall]

set_option maxRecDepth 100000 in
/-- **The calls, by the kernel**: the statements that are not plain. -/
theorem vt_calls : tbStmtsEqb (vtPre.filter fun s ↦ !plainStB s) vtCalls = true := by
  decide +kernel

theorem vt_call_mem {s : Stmt} (hs : s ∈ vtPre) (hp : plainStB s = false) : s ∈ vtCalls := by
  rw [← tbStmtsEqb_sound vt_calls]
  exact List.mem_filter.mpr ⟨hs, by simp [hp]⟩

set_option maxRecDepth 100000 in
/-- The shared tables' pointers: `zeta`, `zeta1` and the exponent table at `g^τ`. -/
theorem vt_sh_muls : ∀ t < 6, tbStmtsEqb [.atom (.mul (.n (709 + 13 * t)) (.n 8) (.n (27 + t))),
    .atom (.mul (.n (710 + 13 * t)) (.n 699) (.n (27 + t))),
    .atom (.mul (.n (711 + 13 * t)) (.n 12) (.n (27 + t)))]
    ((vtPre.drop (701 + 12 * t)).take 3) = true := by
  simp only [vtPre_drop]; decide +kernel

set_option maxRecDepth 100000 in
/-- A framework block's pointers. -/
theorem vt_fw_muls : ∀ b < 3, tbStmtsEqb (vtFwSelT (vtFwW b) b ([25, 26, 821].getD b 0)
    ([none, some 788, some 806].getD b none))
    ((vtPre.drop ([766, 781, 811].getD b 0)).take
      (vtFwSelT (vtFwW b) b ([25, 26, 821].getD b 0) ([none, some 788, some 806].getD b none)).length)
    = true := by
  simp only [vtPre_drop]; decide +kernel

set_option maxRecDepth 100000 in
theorem vt_sel_shapes : (∀ i < 51, (vtPushSel.getD i default).2.2.2.1 < 6 ∧
      777 < (vtPushSel.getD i default).2.2.1 ∧
      (vtPushSel.getD i default).2.2.2.2.2.1 < (vtPushSel.getD i default).2.2.1 + 2 ∧
      (vtPushSel.getD i default).2.2.2.2.2.2.1 < (vtPushSel.getD i default).2.2.1 + 4) ∧
    ∀ i < 45, (vtCountSel.getD i default).2.2.2.1 < 6 ∧ 777 < (vtCountSel.getD i default).2.2.1 ∧
      (vtCountSel.getD i default).2.2.2.2.2.1 < (vtCountSel.getD i default).2.2.1 + 2 ∧
      (vtCountSel.getD i default).2.2.2.2.2.2.1 < (vtCountSel.getD i default).2.2.1 + 4 := by
  decide +kernel

/-! ## Regions -/

/-- The region of the caller's and the own buffers. -/
abbrev VtHonest.reg (H : VtHonest) (B : VtBases) : ℕ → Prop := RegionL (H.linL B ++ H.ownL B)

theorem allocVars_mem {j : ℕ} (hj : j < 111) : vtAllocVars.getD j 0 ∈ vtAllocVars := by
  rw [List.getD_eq_getElem _ _ (by rw [vtAllocVars_length]; exact hj)]
  exact List.getElem_mem _

theorem getD_length_map : ∀ (l : List (List E)) (j : ℕ),
    (l.getD j []).length = (l.map List.length).getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, j + 1 => by simpa using getD_length_map l j

theorem sizes_digits (H : VtHonest) {j : ℕ} (h1 : 12 ≤ j) (h2 : j < 108) : H.sizes.getD j 0 = 9 := by
  unfold VtHonest.sizes
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]

theorem sizes_bits (H : VtHonest) {b : ℕ} (hb : b < 3) : H.sizes.getD (9 + b) 0 = 34 := by
  interval_cases b <;> rfl

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

theorem ptr_own (hw : VtWOk H B w) {j v : ℕ} (hj : j < 111) (hv : vtAllocVars.getD j 0 = v)
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

theorem ptr_own0 (hw : VtWOk H B w) {j v : ℕ} (hj : j < 111) (hv : vtAllocVars.getD j 0 = v)
    {n : ℕ} (h : n ≤ H.sizes.getD j 0) : PtrIn (H.reg B) (w v) n := by
  simpa using ptr_own hw hj hv (a := 0) (n := n) (by omega)

/-! ## The valuation's values -/

local notation "σv" => vtσ rd w (H.args B)

theorem vt_p {i : ℕ} (hi : i < 20) : σv (.n i) = (H.args B).getD i 0 := vt_param rfl hi

theorem vt_s8 : σv (.n 8) = ofK (addressOfIndex B.zeta) := vt_p (by norm_num)

theorem vt_s9 : σv (.n 9) = gen ^ H.μ := vt_p (by norm_num)

theorem vt_s12 : σv (.n 12) = ofK (addressOfIndex B.sq) := vt_p (by norm_num)

theorem vt_s16 : σv (.n 16) = ofK (addressOfIndex B.chi) := vt_p (by norm_num)

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

theorem vt_kbt (I : VtIn H B w rd) {t : ℕ} (ht : t < 6) : σv (.n (27 + t)) = gen ^ H.τ t := by
  have := I.kbsh.1 (2 + t) (by omega)
  rw [show 25 + (2 + t) = 27 + t by omega, show 2 + t = t + 1 + 1 by omega] at this
  rw [this]
  simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
  rw [vtTauList_getD ht]

theorem vt_kb0 (I : VtIn H B w rd) : σv (.n 25) = 1 := by simpa using I.kbsh.1 0 (by norm_num)

theorem vt_kb1 (I : VtIn H B w rd) : σv (.n 26) = gen ^ H.lm := by
  simpa using I.kbsh.1 1 (by norm_num)

theorem vt_nμ (I : VtIn H B w rd) : H.n ≤ H.μ := by
  obtain ⟨t, ht, e⟩ := vt_n_ex I.hs.hr
  rw [← e]; exact I.hs.hτμ t ht

theorem vt_e2500 (I : VtIn H B w rd) : σv (.n 2544) = gen ^ H.n := by
  have g : GoodS rd vtSL w σv
      (fixNe (.atom (.hint (.witness "zc_tau_max" (.stack [.n 2544]))))) :=
    vt_goodS rfl (vt_mem_at 2591 _ (by decide +kernel))
  have := g (.n 2544) (by simp)
  rw [this]; exact I.hw.w2544

/-! ## Each family -/

theorem vt_pw_up (I : VtIn H B w rd) {t : ℕ} (ht : t < 6)
    (h : VSH (coreProgram.Rel rd) rd σv (pwCall t)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (pwCall t) := by
  have h29 : H.τ t < 29 := I.hs.hτ29 t ht
  have hl : vtPadNames.length = 29 := by simp [vtPadNames]
  refine vsh_disp (vt_kbt I ht) (by rw [hl]; exact h29) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtPadNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hc ⊢
  refine padding_weight_relIn h29 ?_ hc
  rw [vt_s8]
  exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) (I.hs.hτμ t ht)

theorem vt_por_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv porCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv porCall := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hl : plusOneRunNames.length = 34 := rfl
  have hm' : H.μ < plusOneRunNames.length := by rw [hl]; omega
  have e703 : σv (.n 699) = w 699 := vt_alloc' (by unfold vtAllocVars; simp)
  refine vsh_disp vt_s9 hm' (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [List.map_cons, List.map_nil] at hc ⊢
  rw [← List.getD_eq_getElem _ "" hm'] at hc ⊢
  refine plus_one_run_relIn (by omega) ?_ ?_ hc
  · rw [e703]
    exact ptr_own0 I.hw (j := 5) (by norm_num) rfl (le_of_eq rfl)
  · rw [vt_s8]
    exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) le_rfl

theorem vt_sh_up (I : VtIn H B w rd) {t : ℕ} (ht : t < 6)
    (h : VSH (coreProgram.Rel rd) rd σv (shCall t)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (shCall t) := by
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  have hμ : H.μ < 33 := I.hs.hμ33
  have hlen := I.kbsh.2 t ht
  have e703 : σv (.n 699) = w 699 := vt_alloc' (by unfold vtAllocVars; simp)
  have e705 : σv (.n 701) = w 701 := vt_alloc' (by unfold vtAllocVars; simp)
  have e706 : σv (.n 702) = w 702 := vt_alloc' (by unfold vtAllocVars; simp)
  obtain ⟨ep, eg⟩ := vtc_shptr (rd := rd) (w := w) (args := H.args B) rfl t ht
  have mem : ∀ s ∈ [Stmt.atom (.mul (.n (709 + 13 * t)) (.n 8) (.n (27 + t))),
      .atom (.mul (.n (710 + 13 * t)) (.n 699) (.n (27 + t))),
      .atom (.mul (.n (711 + 13 * t)) (.n 12) (.n (27 + t)))], s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vt_sh_muls t ht) hs
  have ez := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (709 + 13 * t)) (.n 8) (.n (27 + t)))) (by simp)) (by omega) (by omega)
  have ez1 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (710 + 13 * t)) (.n 699) (.n (27 + t)))) (by simp)) (by omega) (by omega)
  have egs := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (711 + 13 * t)) (.n 12) (.n (27 + t)))) (by simp)) (by omega) (by omega)
  have kb := vt_kbt I ht
  simp only [shCall, vsh_call, List.map_cons, List.map_nil] at h ⊢
  rw [hlen] at h ⊢
  refine shared_selector_tables_relIn (by omega) ?_ ?_ ?_ ?_ ?_ h
  · rw [ep, e705]
    exact ptr_own I.hw (j := 6) (by norm_num) rfl (by
      show 288 * t + 32 * ((H.μ - H.τ t + 3) / 4) ≤ 1728; omega)
  · rw [eg, e706]
    exact ptr_own I.hw (j := 7) (by norm_num) rfl (by
      show 144 * t + 16 * ((H.μ - H.τ t + 3) / 4) ≤ 864; omega)
  · rw [ez, kb, vt_s8]
    exact ptr_lin (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) (by
      show H.τ t + (H.μ - H.τ t) ≤ H.μ; omega)
  · rw [ez1, kb, e703]
    exact ptr_own I.hw (j := 5) (by norm_num) rfl (by
      show H.τ t + (H.μ - H.τ t) ≤ H.μ; omega)
  · rw [egs, kb, vt_s12]
    exact ptr_lin (q := (B.sq, expTableWordsW)) (by simp [VtHonest.linL]) (by
      rw [length_expTableWordsW, show (2 : ℕ) ^ winTabBits = 2048 from rfl]; omega)

/-- Framework block `b`'s `g^κ`. -/
theorem vt_fw_kv (I : VtIn H B w rd) {b : ℕ} (hb : b < 3) :
    σv (.n ([25, 26, 821].getD b 0)) = gen ^ ([0, H.lm, 19].getD b 0) := by
  interval_cases b
  · show σv (.n 25) = gen ^ 0
    rw [vt_kb0 I, pow_zero]
  · exact vt_kb1 I
  · show σv (.n 821) = gen ^ 19
    rw [vt_mulF (H := H) (B := B) (w := w) (rd := rd) (d := 821) (x := 25) (y := 820)
        (vt_mem_at 810 _ (by decide +kernel)) (by norm_num) (by norm_num),
      vt_const (H := H) (B := B) (w := w) (rd := rd) (d := 820) (e := word 524288 0)
        (vt_mem_at 809 _ (by decide +kernel)), show (524288 : ℕ) = 2 ^ 19 by norm_num,
      tb_word_two_pow (by norm_num), vt_kb0 I, one_mul]

theorem vt_fw_up (I : VtIn H B w rd) {b : ℕ} (hb : b < 3)
    (h : VSH (coreProgram.Rel rd) rd σv (fwCall b)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (fwCall b) := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hκ : [0, H.lm, 19].getD b 0 ≤ H.μ := by
    have h1 : H.lm ≤ H.μ := I.hs.hlmμ
    have h2 : 19 ≤ H.μ := I.hs.h19
    interval_cases b <;> simp <;> omega
  have hwv : [25, 26, 821].getD b 0 < vtFwW b ∧ 699 < vtFwW b := by
    interval_cases b <;> simp [vtFwW]
  set κ := [0, H.lm, 19].getD b 0 with hκd
  set kv := [25, 26, 821].getD b 0 with hkv
  set v := vtFwW b with hv
  have mem : ∀ s ∈ vtFwSelT v b kv ([none, some 788, some 806].getD b none), s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vt_fw_muls b hb) hs
  have e0 : σv (.n kv) = gen ^ κ := vt_fw_kv I hb
  have ew : σv (.n v) = gen ^ (H.μ - κ) := by
    rw [vt_mulB (mem (.atom (.mul (.n 9) (.n v) (.n kv))) (by simp [vtFwSelT])) (by omega),
      vt_s9, e0, gen_div hκ]
  have e7 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 7)) (.n (v + 6)) (.n kv))) (by simp [vtFwSelT])) (by omega)
    (by omega)
  have e8 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 8)) (.n 699) (.n kv))) (by simp [vtFwSelT])) (by omega) (by omega)
  have e9 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 9)) (.n 664) (.n kv))) (by simp [vtFwSelT])) (by omega) (by omega)
  have hjv : vtAllocVars.getD (9 + b) 0 = v + 6 := vtAllocVars_F b hb
  have a6 : σv (.n (v + 6)) = w (v + 6) := by
    rw [← hjv]; exact vt_alloc' (allocVars_mem (by omega))
  have a703 : σv (.n 699) = w 699 := vt_alloc' (by unfold vtAllocVars; simp)
  have a668 : σv (.n 664) = w 664 := vt_alloc' (by unfold vtAllocVars; simp)
  have hl : vtBsNames.length = 34 := by simp [vtBsNames]
  refine vsh_disp ew (by rw [hl]; omega) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtBsNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine block_selector_relIn (by omega) ?_ ?_ ?_ hc
  · rw [e7, a6, e0]
    exact ptr_own I.hw (j := 9 + b) (by omega) hjv (by rw [sizes_bits H hb]; omega)
  · rw [e8, a703, e0]
    exact ptr_own I.hw (j := 5) (by norm_num) rfl (by
      show κ + (H.μ - κ) ≤ H.μ; omega)
  · rw [e9, a668, e0]
    exact ptr_own I.hw (j := 4) (by norm_num) rfl (by
      show κ + (H.μ - κ) ≤ 34; omega)

theorem vt_im_up (I : VtIn H B w rd) {b r : ℕ} (hb : b = 1 ∨ b = 2)
    (h : VSH (coreProgram.Rel rd) rd σv (imCall ([25, 26, 821].getD b 0) r)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (imCall ([25, 26, 821].getD b 0) r) := by
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
    (h : TbReadsAt rd sb (offDigits off τ)) :
    ∀ k < btN n, ∃ u < 2 ^ btW n k, LoadHolds rd sb k (gen ^ u) := by
  intro k hk
  have hr := offDigits_reads hn hob h
  have hbl : (selBitsOf off τ n).length = n := selBitsOf_length _ _ _
  have hlen : k < (nibDigits (selBitsOf off τ n)).length := by
    simp only [nibDigits, List.length_map, List.length_range, hbl]; exact hk
  refine ⟨btkU n (selBitsOf off τ n) k, btkU_lt _ _ _, ?_⟩
  have := hr k hlen
  rwa [← List.getD_eq_getElem _ 0 hlen, btk_digit hbl hk] at this

theorem vt_sel_up (I : VtIn H B w rd) {x : ℕ × ℕ × ℕ × ℕ × Option ℕ × ℕ × ℕ × ℕ}
    (hchk : tbStmtsEqb (vtSelT x.2.2.1 x.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2)
      ((vtAt x.2.1).take (vtSelT x.2.2.1 x.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
        x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2).length) = true)
    (ht : x.2.2.2.1 < 6) (hw0 : 777 < x.2.2.1) (hes : x.2.2.2.2.2.1 < x.2.2.1 + 2)
    (hgs : x.2.2.2.2.2.2.1 < x.2.2.1 + 4)
    (hd : 0 < x.2.2.2.1 → x.2.2.2.2.2.1 = vtEqV (x.2.2.2.1 - 1) ∧
      ((x.2.2.2.2.2.2.1 = vtGV (x.2.2.2.1 - 1) ∧ x.2.2.2.2.2.2.2 = 21299200) ∨
        (x.2.2.2.1 = 2 ∧ x.2.2.2.2.2.2.1 = 702 ∧ x.2.2.2.2.2.2.2 = 299140177199104)))
    {j : ℕ} (hj1 : 12 ≤ j) (hj : j < 108) (hjv : vtAllocVars.getD j 0 = x.2.2.1) {off : ℕ}
    (hob : off < 2 ^ H.μ)
    (hdig : TbReadsAt rd (w x.2.2.1) (offDigits off (H.τ x.2.2.2.1)))
    (h : VSH (coreProgram.Rel rd) rd σv (selCall x)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (selCall x) := by
  obtain ⟨b, pos, v, t, prev, es, gs, gw⟩ := x
  simp only at hchk ht hw0 hes hgs hd hjv hdig
  have hμ : H.μ < 33 := I.hs.hμ33
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  have mem : ∀ s ∈ vtSelT v b t prev es gs gw, s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vtPre_drop pos ▸ hchk) hs
  have a705 : σv (.n 701) = w 701 := vt_alloc' (by unfold vtAllocVars; simp)
  have a706 : σv (.n 702) = w 702 := vt_alloc' (by unfold vtAllocVars; simp)
  have av : σv (.n v) = w v := by
    rw [← hjv]; exact vt_alloc' (allocVars_mem (by omega))
  have eqt : σv (.n (if t = 0 then 701 else v + 2)) = w 701 * gen ^ (288 * t) := by
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp [a705]
    · have ht0 : t ≠ 0 := by omega
      obtain ⟨rfl, -⟩ := hd h0
      obtain ⟨e1, -⟩ := vtc_shptr (rd := rd) (w := w) (args := H.args B) rfl (t - 1) (by omega)
      simp only [ht0, ↓reduceIte]
      rw [vt_mulF (mem (.atom (.mul (.n (v + 2)) (.n (vtEqV (t - 1))) (.n (v + 1))))
          (by simp [vtSelT, ht0])) hes (by omega),
        vt_const (mem (.atom (.const (.n (v + 1)) vtW288)) (by simp [vtSelT, ht0])), e1, a705,
        show vtW288 = gen ^ 288 from vtW288_eq, mul_assoc, ← pow_add,
        show 288 * (t - 1) + 288 = 288 * t by omega]
  have egt : σv (.n (if t = 0 then 702 else v + 4)) = w 702 * gen ^ (144 * t) := by
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp [a706]
    · have ht0 : t ≠ 0 := by omega
      have e4 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
        (mem (.atom (.mul (.n (v + 4)) (.n gs) (.n (v + 3)))) (by simp [vtSelT, ht0])) hgs
        (by omega)
      have c3 := vt_const (H := H) (B := B) (w := w) (rd := rd)
        (mem (.atom (.const (.n (v + 3)) (word gw 0))) (by simp [vtSelT, ht0]))
      simp only [ht0, ↓reduceIte]
      rw [e4, c3]
      rcases (hd h0).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨-, e2⟩ := vtc_shptr (rd := rd) (w := w) (args := H.args B) rfl (t - 1) (by omega)
        rw [e2, a706, vtW144_eq, mul_assoc, ← pow_add,
          show 144 * (t - 1) + 144 = 144 * t by omega]
      · rw [a706, vtW288_eq]
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
  · rw [eqt]
    exact ptr_own I.hw (j := 6) (by norm_num) rfl (by
      show 288 * t + 32 * btN (H.μ - H.τ t) ≤ 1728; simp only [btN]; omega)
  · rw [egt]
    exact ptr_own I.hw (j := 7) (by norm_num) rfl (by
      show 144 * t + 16 * btN (H.μ - H.τ t) ≤ 864; simp only [btN]; omega)

theorem vt_loop_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv loopCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv loopCall := by
  unfold loopCall at h ⊢
  refine ⟨h.1, fun hne ↦ ?_⟩
  have hc := h.2 hne
  have e2500 := vt_e2500 I
  have e2597 : σv (.n 2635) = 1 + gen ^ H.n := by
    rw [vt_add (d := 2635) (x := 2634) (y := 2544) (vt_mem_at 2665 _ (by decide +kernel)),
      vt_const (vt_mem_at 2664 (.atom (.const (.n 2634) (word 1 0))) (by decide +kernel)),
      tb_word_one, e2500]
  have e2598 : σv (.n 2636) = gen ^ 0 := by
    rw [vt_const (vt_mem_at 2666 (.atom (.const (.n 2636) (word 1 0))) (by decide +kernel)),
      tb_word_one, pow_zero]
  have hK : 0 < H.n := by
    rcases Nat.eq_zero_or_pos H.n with h0 | h0
    · exact absurd (by rw [e2597, h0, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
    · exact h0
  have a2589 : σv (.n 2627) = w 2627 := vt_alloc' (by unfold vtAllocVars; simp)
  have a2592 : σv (.n 2630) = w 2630 := vt_alloc' (by unfold vtAllocVars; simp)
  simp only [List.map_cons, List.map_nil] at hc ⊢
  rw [e2598, e2500, a2589, a2592, vt_s16] at hc ⊢
  obtain ⟨d, hd⟩ := hc
  -- the rounds' cursor words
  have hR : TbReadsAt rd (w 2627)
      (zcRoundsW H.cap0 H.target (ofK (addressOfIndex B.cur) * gen ^ 13 * gen) H.xsR H.n) := by
    have := vt_own_reads I.hm I.hw (j := 108 + 0) (by norm_num)
    rw [ownW_getD_Z H B (k := 0) (by norm_num), show vtAllocVars.getD (108 + 0) 0 = 2627 by decide]
      at this
    exact this
  have hcur : ∀ k < H.n, ∀ c, LoadHolds rd (w 2627 * gen ^ (7 * k)) 5 c →
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
  refine loop10_relIn hK ?_ ?_ ?_ hcur d 0 hK hd
  · exact ptr_own0 I.hw (j := 108) (by norm_num) (by decide) le_rfl
  · exact ptr_lin0 (q := (B.chi, H.chiW)) (by simp [VtHonest.linL]) (by
      simp [VtHonest.chiW, zcChis])
  · exact ptr_own0 I.hw (j := 109) (by norm_num) (by decide) le_rfl

theorem vt_epc_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv epcCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv epcCall := by
  have e2500 := vt_e2500 I
  have a2613 : σv (.n 2651) = w 2651 := vt_alloc' (by unfold vtAllocVars; simp)
  have a703 : σv (.n 699) = w 699 := vt_alloc' (by unfold vtAllocVars; simp)
  have hnμ := vt_nμ I
  have hμ : H.μ < 33 := I.hs.hμ33
  simp only [epcCall, vsh_call, List.map_cons, List.map_nil] at h ⊢
  rw [e2500] at h ⊢
  refine eq_prefix_chain_relIn (by omega) ?_ ?_ ?_ h
  · rw [a2613]; exact ptr_own0 I.hw (j := 110) (by norm_num) (by decide) le_rfl
  · rw [vt_s16]
    exact ptr_lin0 (q := (B.chi, H.chiW)) (by simp [VtHonest.linL]) (by
      simp [VtHonest.chiW, zcChis])
  · rw [a703]; exact ptr_own0 I.hw (j := 5) (by norm_num) (by decide) hnμ

/-- The tail rounds' cursors: `7 + 2k` words into the stream. -/
theorem vt_otr_cursor (I : VtIn H B w rd) {k : ℕ} (hk : k < 3) :
    σv (.n ([1875, 1881, 1889].getD k 0)) = ofK (addressOfIndex B.cur) * gen ^ (7 + 2 * k) := by
  interval_cases k
  · show σv (.n 1875) = _
    rw [vt_mulF (H := H) (B := B) (w := w) (rd := rd) (d := 1875) (x := 5) (y := 1874)
        (vt_mem_at 1939 _ (by decide +kernel)) (by norm_num) (by norm_num),
      vt_const (H := H) (B := B) (w := w) (rd := rd) (d := 1874) (e := word 128 0)
        (vt_mem_at 1938 _ (by decide +kernel)), show (128 : ℕ) = 2 ^ 7 by norm_num,
      tb_word_two_pow (by norm_num), vt_p (by norm_num)]
    rfl
  · show σv (.n 1881) = _
    have g : GoodS rd vtSL w σv (otrCall 0) := vt_goodS rfl (vt_mem_at 1940 (otrCall 0) (by decide +kernel))
    have e := g (.n 1881) (List.mem_map.mpr ⟨5, List.mem_range.mpr (by norm_num), rfl⟩)
    have h1 := congrArg (fun l ↦ l.getD 5 0) I.hw.hw1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
      show (5 : ℕ) < 8 from by norm_num, Option.map_some, Option.getD_some] at h1
    rw [e, show (V.n 1881).idx = 1876 + 5 from rfl, h1, List.getElem?_append_right
      (by simp [vtBcR1, bcRound, Fs.squeeze, capOf])]
    simp only [List.length_cons, List.length_nil, vtBcR1, bcRound, Fs.squeeze, capOf]
    show (H.args B).getD 5 0 * gen ^ 7 * gen ^ 2 = _
    show ofK (addressOfIndex B.cur) * gen ^ 7 * gen ^ 2 = _
    ring
  · show σv (.n 1889) = _
    have g : GoodS rd vtSL w σv (otrCall 1) := vt_goodS rfl (vt_mem_at 1942 (otrCall 1) (by decide +kernel))
    have e := g (.n 1889) (List.mem_map.mpr ⟨5, List.mem_range.mpr (by norm_num), rfl⟩)
    have h1 := congrArg (fun l ↦ l.getD 5 0) I.hw.hw2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
      show (5 : ℕ) < 8 from by norm_num, Option.map_some, Option.getD_some] at h1
    rw [e, show (V.n 1889).idx = 1884 + 5 from rfl, h1, List.getElem?_append_right
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
    · obtain ⟨d1, -, -, -, -, d6⟩ := vt_pushSel_data i hi
      refine vt_sel_up I (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
        (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2.1 (hP i hi).2.2.2 d6 (j := 12 + i) (by omega)
        (by omega) (vtAllocVars_P i hi)
        (off := H.offP.getD (3 + i) 0)
        (vtB_stack_lt (vtSizesP H.lm (vtHt H.rows)) (b := 3 + i) (by rw [vtSizesP_length]; omega)
          hfitP) ?_ hv
      exact vt_own_reads' hm hw (j := 12 + i) (by omega) (vtAllocVars_P i hi)
        (ownW_getD_P H B hi)
    · obtain ⟨d1, -, -, -, -, d6⟩ := vt_countSel_data i hi
      refine vt_sel_up I (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
        (hC i hi).1 (hC i hi).2.1 (hC i hi).2.2.1 (hC i hi).2.2.2 d6 (j := 63 + i) (by omega)
        (by omega) (vtAllocVars_C i hi)
        (off := H.offC.getD i 0)
        (vtB_stack_lt (vtSizesC (vtHt H.rows)) (b := i) (by rw [vtSizesC_length]; omega)
          hfitC) ?_ hv
      exact vt_own_reads' hm hw (j := 63 + i) (by omega) (vtAllocVars_C i hi)
        (ownW_getD_C H B hi)
    · exact vt_otr_up I (k := 0) (by norm_num) hv
    · exact vt_otr_up I (k := 1) (by norm_num) hv
    · exact vt_otr_up I (k := 2) (by norm_num) hv
    · exact vt_loop_up I hv
    · exact vt_epc_up I hv
  · exact vsh_plain hp hv

end
end LeanVM.Guest.B1.Tables
