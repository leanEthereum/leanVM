/-
  LeanVM.Guest.Budget.MvCount

  `main`'s `da_verify` and `claim_list_digest`, their instructions per opcode by their trees'
  shapes (B1's `Da.dvNH`, `Main.clHonest`): each callee by its static count from the `V` count
  certificates (`Count/MvCountData`), each loop by its iterations.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.MvCountChkX
public import LeanVM.Guest.Count.MvCountChkM
public import LeanVM.Guest.Count.MvCountChkS
public import LeanVM.Guest.Count.MvCountChkD
public import LeanVM.Guest.Count.MvCountChkJ
public import LeanVM.Guest.Count.MvCountChkK
public import LeanVM.Guest.Budget.VsCount
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.Count.Static
public import LeanVM.Guest.B1.Da.DvAt
public import LeanVM.Guest.B1.Main.MainGoalsClT

/-!
# `da_verify`'s and the claim lists' instructions

`colW op r`: a column's instructions of `op` on `r` blobs: its frame's weight, its weights'
expansion's (`da_expand__L7_L8`), its row loop's `r` iterations (`col_weight_le`, on a tree of
`Da.colNH r`). `l18From_weight_le`: the column loop's `n` iterations, each its frame and a column.
`dvW op r L`: `da_verify`'s on `r` blobs padded to `2^L`: its frame, the row shape's and
`da_vector`'s, the regions' bases' `r` iterations, `128` columns, the blobs' trees' `r`, the
padding's `2^L - r` and the levels at `L` (`dv_weight_le`, on a tree of `Da.dvNH r L`);
`dvW_le`: within `kcDvA op + kcDvR op · r + kcDvP op · 2^L`.
`clW op n`: `claim_list_digest`'s on `n` claims, its frame's, `list_split`'s, `n / 136` iterations
of `claim_list_digest_loop0`, `n % 136 / 17` of `claim_list_digest_loop1` and the last group's `claim_list_last__L{n % 17}`
(`cl_weight_le`, on a tree of
`Main.clHonest n`); `clW_le`: within `kcClA op + kcClS op · n`. `Count.mainCounts op`: `main`'s callees' weights at
`op`'s instructions, the static ones' certificates and these two by their shapes.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem mvTab_ok (op : Opcode) : mvTabOk op = true := by
  cases op
  · exact mvTab_ok_x
  · exact mvTab_ok_m
  · exact mvTab_ok_s
  · exact mvTab_ok_d
  · exact mvTab_ok_j
  · exact mvTab_ok_k

theorem mvTab_parts (op : Opcode) :
    (∀ i < 3, (kvOkB op (dvStJ.getD i 0) (dvStNames.getD i "") &&
      kvSBJ op (dvStJ.getD i 0) == (kcDvStT op).getD i 0) = true) ∧
    (∀ i < 4, (kvOkK op (dvLpJ.getD i 0) (dvLpNames.getD i "") &&
      kvSKJ op (dvLpJ.getD i 0) == (kcDvLpT op).getD i 0) = true) ∧
    (∀ L < 11, (kvOkB op (dlJ.getD L 0) (B1.Da.dlNames.getD L "") &&
      kvSBJ op (dlJ.getD L 0) == (kcDlT op).getD L 0) = true) ∧
    (∀ k < 17, (kvOkB op (clJ.getD k 0) (B1.Digest.clNames.getD k "") &&
      kvSBJ op (clJ.getD k 0) == (kcClT op).getD k 0) = true) ∧
    (∀ i < 2, (kvOkK op (clLpJ.getD i 0) (clLpNames.getD i "") &&
      kvSKJ op (clLpJ.getD i 0) == (kcClLpT op).getD i 0) = true) ∧
    (∀ i < 4, decide ((coreProgram[mvOmJ.getD i 0]?).map Fn.name = some (mvOmNames.getD i "")) = true ∧
      (B2C.plumbOf (mvOmJ.getD i 0 + 1)).pmax.getD (B2C.opIdx op) 0 = (mvOmT op).getD i 0) := by
  have h := mvTab_ok op
  simp only [mvTabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun L hL => ?_, fun k hk => ?_, fun i hi => ?_,
    fun i hi => h6 i hi⟩
  · have := h1 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h2 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h3 L hL; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h4 k hk; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h5 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this

variable (op : Opcode)

/-- **`da_verify`'s static callees** but the levels by `L`. -/
theorem dvSt_weightLe {i : ℕ} (hi : i < 3) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (dvStNames.getD i "")
      fun _ => (kcDvStT op).getD i 0 :=
  weightLe_tab ((mvTab_parts op).1 i hi)

/-- **`da_verify`'s and its columns' loops, per iteration.** -/
theorem dvLp_loop {i : ℕ} (hi : i < 4) :
    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) (dvLpNames.getD i "") ((kcDvLpT op).getD i 0) :=
  loopWeightLe_tab ((mvTab_parts op).2.1 i hi)

/-- **The DA levels at `L`.** -/
theorem dl_weightLe {L : ℕ} (hL : L < 11) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (B1.Da.dlNames.getD L "")
      fun _ => (kcDlT op).getD L 0 :=
  weightLe_tab ((mvTab_parts op).2.2.1 L hL)

/-- **`claim_list_last__L{k}`.** -/
theorem cl_weightLe {k : ℕ} (hk : k < 17) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (B1.Digest.clNames.getD k "")
      fun _ => (kcClT op).getD k 0 :=
  weightLe_tab ((mvTab_parts op).2.2.2.1 k hk)

/-- The claim lists' loops' instructions per iteration: `claim_list_digest_loop0` per `136` claims, `claim_list_digest_loop1`
per `17`. -/
def kcL15 : ℕ := (kcClLpT op).getD 0 0

/-- See `kcL15`. -/
def kcL16 : ℕ := (kcClLpT op).getD 1 0

/-- **`claim_list_digest_loop0`, per iteration.** -/
theorem l15_loop : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) (name% claim_list_digest_loop0) (kcL15 op) :=
  loopWeightLe_tab (by simpa [clLpNames, kcL15] using (mvTab_parts op).2.2.2.2.1 0 (by norm_num))

/-- **`claim_list_digest_loop1`, per iteration.** -/
theorem l16_loop : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) (name% claim_list_digest_loop1) (kcL16 op) :=
  loopWeightLe_tab (by simpa [clLpNames, kcL16] using (mvTab_parts op).2.2.2.2.1 1 (by norm_num))

/-- **The frame weights** of `mvOmNames`. -/
theorem mvOm_eq {i : ℕ} (hi : i < 4) :
    B2C.ωArm B2C.xmssArmC op (mvOmNames.getD i "") = (mvOmT op).getD i 0 := by
  obtain ⟨hn, hv⟩ := (mvTab_parts op).2.2.2.2.2 i hi
  rw [ωArm_idx (decide_eq_true_eq.mp hn) (by interval_cases i <;> decide), hv]

theorem dlNames_bang {L : ℕ} (hL : L < 11) : B1.Da.dlNames[L]! = B1.Da.dlNames.getD L "" := by
  interval_cases L <;> decide

theorem clNames_bang {k : ℕ} (hk : k < 17) :
    B1.Digest.clNames[k]! = B1.Digest.clNames.getD k "" := by
  interval_cases k <;> decide

theorem clNames_ne {k : ℕ} (hk : k < 17) :
    B1.Digest.clNames[k]! ≠ "list_split" ∧ B1.Digest.clNames[k]! ≠ (name% claim_list_digest_loop0) ∧
      B1.Digest.clNames[k]! ≠ (name% claim_list_digest_loop1) := by
  interval_cases k <;> decide

/-- A loop of `r` iterations from the counter `1`, at most `r` per-iteration counts. -/
theorem loop_at {ω : String → ℕ} {f : String} {K : ℕ} (hL : LoopWeightLe ω f K) {rd : Reader}
    {t : Tree} {args rets : List E} {r : ℕ} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (h0 : args.getD 0 0 = 1) (h1 : args.getD 1 0 = gen ^ r)
    (hr : 0 < r) (hr64 : r < 2 ^ 64 - 1) : t.weight ω ≤ r * K := by
  have := hL rd t args rets 0 r hn hv hb (by rw [h0, one_eq_ofK])
    (by rw [h1, Value.gen_pow_eq_ofK]) hr hr64
  simpa using this

/-! ## A column and the column loop -/

/-- **A column's instructions** on `r` rows: its frame, its weights' expansion, its row loop's `r`
iterations. -/
def colW (r : ℕ) : ℕ :=
  (mvOmT op).getD 2 0 + (kcDvStT op).getD 2 0 + r * (kcDvLpT op).getD 3 0

/-- **A column's instructions** on a tree of its honest shape. -/
theorem col_weight_le {r : ℕ} (hr : 0 < r) (hr' : r ≤ 1024) {rd : Reader} {t : Tree}
    {args rets : List E} (h : B1.Da.colNH r t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ colW op r := by
  obtain ⟨σ, ks, rfl, ⟨h1, h17⟩, hc, hl, hT⟩ := h
  rw [B1.Da.col_flatCalls] at hc hl hT
  obtain ⟨hk, hbk⟩ := node_kids hv hb hc
  have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) _ [fun _ => True, fun _ => True]
    [(kcDvStT op).getD 2 0, r * (kcDvLpT op).getD 3 0] ks hk hbk hT
    (by simp [B1.Da.colCallsS]) (by simp [B1.Da.colCallsS])
    (fun i hi _ _ ht t' rets' hn hv' hb' _ => by
      have hi2 : i < 2 := by simpa [B1.Da.colCallsS] using hi
      interval_cases i <;>
        simp only [B1.Da.colCallsS, List.map_cons, List.map_nil, mkCall, List.getElem_cons_zero,
          List.getElem_cons_succ] at ht hn hv' ⊢
      · exact dvSt_weightLe op (i := 2) (by norm_num) rd t' _ rets' hn hv' hb'
      · exact loop_at (dvLp_loop op (i := 3) (by norm_num)) hn hv' hb' (by simp [h17])
          (by simp [h1]) hr (by omega))
  have hom := mvOm_eq op (i := 2) (by norm_num)
  rw [Tree.weight]
  simp only [List.sum_cons, List.sum_nil] at hk'
  rw [show B2C.ωArm B2C.xmssArmC op "da_verify_column" = (mvOmT op).getD 2 0 from hom]
  unfold colW
  omega

/-- **The column loop's `n` iterations** weigh at most `n` times its frame and a column's bound. -/
theorem l18From_weight_le {Tc : Tree → Prop} {Kc : ℕ}
    (hc : ∀ (rd : Reader) (t : Tree) (args rets : List E), Tc t → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight (B2C.ωArm B2C.xmssArmC op) ≤ Kc) :
    ∀ (n k : ℕ) (rd : Reader) (t : Tree) (args rets : List E), B1.Da.l18From Tc n k t →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ n * (B2C.ωArm B2C.xmssArmC op (name% da_verify_loop1) + Kc)
  | 0, _, _, _, _, _, h, _, _ => h.elim
  | n + 1, k, rd, t, args, rets, h, hv, hb => by
    obtain ⟨σ, ks, rfl, -, hcl, hl, hT⟩ := h
    obtain ⟨hk, hbk⟩ := node_kids hv hb hcl
    have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) (B1.Da.l18Calls k)
      [Tc, B1.Da.l18From Tc n (k + 1)] [Kc, n * (B2C.ωArm B2C.xmssArmC op (name% da_verify_loop1) + Kc)] ks hk
      hbk hT (by simp [B1.Da.l18Calls]) (by simp [B1.Da.l18Calls])
      (fun i hi _ _ _ t' rets' _ hv' hb' hT' => by
        have hi2 : i < 2 := by simpa [B1.Da.l18Calls] using hi
        interval_cases i <;>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hT' ⊢
        · exact hc rd t' _ rets' hT' hv' hb'
        · exact l18From_weight_le hc n (k + 1) rd t' _ rets' hT' hv' hb')
    rw [Tree.weight]
    simp only [List.sum_cons, List.sum_nil] at hk'
    rw [Nat.succ_mul]
    omega

/-! ## `da_verify` -/

/-- **`da_verify`'s instructions of `op`** on `r` rows padded to `2^L`: its frame, the row shape,
the dual codeword, the regions' bases, `128` columns, the blobs' trees, the padding, the roots'
tree. -/
def dvW (r L : ℕ) : ℕ :=
  (mvOmT op).getD 0 0 + (kcDvStT op).getD 0 0 + (kcDvStT op).getD 1 0 + r * (kcDvLpT op).getD 0 0 +
    128 * ((mvOmT op).getD 1 0 + colW op r) + r * (kcDvLpT op).getD 1 0 +
    (2 ^ L - r) * (kcDvLpT op).getD 2 0 + (kcDlT op).getD L 0

/-- **`da_verify`'s instructions of `op`** on a tree of its honest shape `Da.dvNH r L`. -/
theorem dv_weight_le {r L : ℕ} (hr : 0 < r) (hr' : r ≤ 1024) (hrL : r ≤ 2 ^ L) (hL : L < 11)
    {rd : Reader} {t : Tree} {args rets : List E} (h : B1.Da.dvNH r L t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ dvW op r L := by
  obtain ⟨σ, ks, rfl, ⟨h1, h2, h4, h35, h42, h44, h45⟩, hc, hl, hT⟩ := h
  have h2L : 2 ^ L < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hL
  have hlog : logG (σ (.n 2)) = L := by rw [h2]; exact logG_gen_pow (by omega)
  rw [B1.Da.dv_flatCalls, hlog] at hc hl hT
  obtain ⟨hk, hbk⟩ := node_kids hv hb hc
  have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) _ (B1.Da.dvTs r)
    [(kcDvStT op).getD 0 0, (kcDvStT op).getD 1 0, r * (kcDvLpT op).getD 0 0,
      128 * (B2C.ωArm B2C.xmssArmC op (name% da_verify_loop1) + colW op r), r * (kcDvLpT op).getD 1 0,
      (2 ^ L - r) * (kcDvLpT op).getD 2 0, (kcDlT op).getD L 0] ks hk hbk hT
    (by simp [B1.Da.dvCallsS, B1.Da.dvTs]) (by simp [B1.Da.dvCallsS])
    (fun i hi _ _ ht t' rets' hn hv' hb' hT' => by
      have hi7 : i < 7 := by simpa [B1.Da.dvCallsS] using hi
      interval_cases i <;>
        simp only [B1.Da.dvCallsS, B1.Da.dvTs, List.map_cons, List.map_nil, mkCall,
          List.getElem_cons_zero, List.getElem_cons_succ] at ht hn hv' hT' ⊢
      · exact dvSt_weightLe op (i := 0) (by norm_num) rd t' _ rets' hn hv' hb'
      · exact dvSt_weightLe op (i := 1) (by norm_num) rd t' _ rets' hn hv' hb'
      · exact loop_at (dvLp_loop op (i := 0) (by norm_num)) hn hv' hb' (by simp [h35])
          (by simp [h1]) hr (by omega)
      · exact l18From_weight_le op (fun rd t args rets hT hv hb => col_weight_le op hr hr' hT hv hb)
          128 0 rd t' _ rets' hT' hv' hb'
      · exact loop_at (dvLp_loop op (i := 1) (by norm_num)) hn hv' hb' (by simp [h42])
          (by simp [h1]) hr (by omega)
      · have hg : 2 ^ L - r ≠ 0 := by
          have := of_decide_eq_true ht
          rw [h44] at this
          exact (B1.Da.one_add_gen_ne_iff (by unfold B1.ordG; omega)).mp this
        exact loop_at (dvLp_loop op (i := 2) (by norm_num)) hn hv' hb' (by simp [h45])
          (by simp [h4]) (by omega) (by omega)
      · rw [B1.Da.dlList_getD (by omega), ← B1.Da.dlNames_bang (by omega), dlNames_bang hL] at hn
        exact dl_weightLe op hL rd t' _ rets' hn hv' hb')
  have hom := mvOm_eq op (i := 0) (by norm_num)
  have hom1 := mvOm_eq op (i := 1) (by norm_num)
  rw [Tree.weight]
  simp only [List.sum_cons, List.sum_nil] at hk'
  rw [show B2C.ωArm B2C.xmssArmC op "da_verify" = (mvOmT op).getD 0 0 from hom]
  rw [show B2C.ωArm B2C.xmssArmC op (name% da_verify_loop1) = (mvOmT op).getD 1 0 from hom1] at hk'
  unfold dvW
  omega

/-- **`da_verify`'s instructions on `r` rows padded to `2^L`** within
`kcDvA op + kcDvR op · r + kcDvP op · 2^L`. -/
theorem dvW_le {r L : ℕ} (hlo : r ≤ 2 ^ L) (hL : L < 11) :
    dvW op r L ≤ kcDvA op + kcDvR op * r + kcDvP op * 2 ^ L := by
  unfold dvW colW
  cases op <;> interval_cases L <;>
    simp only [mvOmT, kcDvStT, kcDvLpT, kcDlT, kcDvA, kcDvR, kcDvP, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reducePow] at hlo ⊢ <;> omega

/-! ## The claim lists -/

/-- **`claim_list_digest`'s instructions of `op` on `n = 136a + 17b + c` claims**: its frame's,
`list_split`'s, `a` iterations of `claim_list_digest_loop0`, `b` of `claim_list_digest_loop1` and `claim_list_last__L{c}`. -/
def clW (n : ℕ) : ℕ :=
  (mvOmT op).getD 3 0 + (if n = 0 then 0 else
    kcLs op + n / 136 * kcL15 op + n % 136 / 17 * kcL16 op + (kcClT op).getD (n % 17) 0)

/-- **`claim_list_digest`'s instructions** on a tree of honest shape. -/
theorem cl_weight_le {n : ℕ} (hn : n / 17 < 2 ^ 64 - 1) {rd : Reader} {t : Tree}
    {args rets : List E} (h : B1.Main.clHonest n t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ clW op n := by
  let W : Call → ℕ := fun c =>
    if c.f = "list_split" then kcLs op
    else if c.f = (name% claim_list_digest_loop0) then n / 136 * kcL15 op
    else if c.f = (name% claim_list_digest_loop1) then n % 136 / 17 * kcL16 op else (kcClT op).getD (n % 17) 0
  obtain ⟨σ, -, hle⟩ := NodeHonest.weight_le (B2C.ωArm B2C.xmssArmC op) (fun _ => W) h hv hb
    (by
      intro σ hQ c T hmem ht t' rets' hn' hv' hb' _
      by_cases h0 : n = 0
      · simp [B1.Digest.clCalls, h0] at hmem
      obtain ⟨-, h23, h24, -, -, h50, h70⟩ := And.intro hQ.1 (hQ.2 h0)
      simp only [B1.Digest.clCalls, h0, ↓reduceIte, B1.Digest.clTs, List.zip_cons_cons,
        List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [W, ↓reduceIte]
        exact ls_weightLe op rd t' _ rets' hn' hv' hb'
      · simp only [W, String.reduceEq, ↓reduceIte]
        have hq : n / 136 ≠ 0 := by simpa using ht
        exact loop_at (l15_loop op) hn' hv' hb' (by simp [h50]) (by simp [h23]) (by omega)
          (by omega)
      · simp only [W, String.reduceEq, ↓reduceIte]
        have hq : n % 136 / 17 ≠ 0 := by simpa using ht
        exact loop_at (l16_loop op) hn' hv' hb' (by simp [h70]) (by simp [h24]) (by omega)
          (by omega)
      · have hk : n % 17 < 17 := Nat.mod_lt _ (by norm_num)
        obtain ⟨e1, e2, e3⟩ := clNames_ne hk
        simp only [W, e1, e2, e3, ↓reduceIte]
        rw [clNames_bang hk] at hn'
        exact cl_weightLe op hk rd t' _ rets' hn' hv' hb')
  have hom := mvOm_eq op (i := 3) (by norm_num)
  simp only [mvOmNames, List.getD_cons_succ, List.getD_cons_zero] at hom
  rw [hom] at hle
  unfold clW
  by_cases h0 : n = 0
  · have hc : callsW W (B1.Digest.clCalls n σ) = 0 := by simp [callsW, B1.Digest.clCalls, h0]
    simp only [h0, ↓reduceIte]
    omega
  · have hc : callsW W (B1.Digest.clCalls n σ) ≤
        kcLs op + n / 136 * kcL15 op + n % 136 / 17 * kcL16 op + (kcClT op).getD (n % 17) 0 := by
      have hk := Nat.mod_lt n (show 0 < 17 by norm_num)
      obtain ⟨e1, e2, e3⟩ := clNames_ne hk
      simp only [callsW, B1.Digest.clCalls, h0, ↓reduceIte, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, W, String.reduceEq, e1, e2, e3]
      clear hle
      generalize n / 136 * kcL15 op = P
      generalize n % 136 / 17 * kcL16 op = Q
      split <;> split <;> omega
    simp only [h0, ↓reduceIte]
    omega

theorem kcClA_eq : kcClA op =
    (mvOmT op).getD 3 0 + kcLs op + 7 * kcL16 op + (kcClT op).foldl max 0 := by
  cases op <;> decide

theorem kcClS_eq : kcClS op = (kcL15 op + 135) / 136 := by
  cases op <;> decide

/-- **`claim_list_digest`'s instructions** within `kcClA op + kcClS op · n`: at most `7`
iterations of `claim_list_digest_loop1` (`n % 136 / 17 ≤ 7`) and the largest last group in the constant. -/
theorem clW_le (n : ℕ) : clW op n ≤ kcClA op + kcClS op * n := by
  rw [kcClA_eq, kcClS_eq]
  unfold clW
  split
  · omega
  · have hk : (kcClT op).getD (n % 17) 0 ≤ (kcClT op).foldl max 0 := by
      cases op <;> (have : n % 17 < 17 := Nat.mod_lt _ (by norm_num); interval_cases (n % 17) <;> decide)
    have hq : n / 136 * kcL15 op ≤ (kcL15 op + 135) / 136 * n := by
      have h1 : kcL15 op ≤ 136 * ((kcL15 op + 135) / 136) := by omega
      have h2 : 136 * (n / 136) ≤ n := Nat.mul_div_le n 136
      calc n / 136 * kcL15 op ≤ n / 136 * (136 * ((kcL15 op + 135) / 136)) :=
            Nat.mul_le_mul_left _ h1
        _ = 136 * (n / 136) * ((kcL15 op + 135) / 136) := by ring
        _ ≤ n * ((kcL15 op + 135) / 136) := Nat.mul_le_mul_right _ h2
        _ = (kcL15 op + 135) / 136 * n := Nat.mul_comm _ _
    have hb : n % 136 / 17 * kcL16 op ≤ 7 * kcL16 op := Nat.mul_le_mul_right _ (by omega)
    omega

end
end LeanVM.Guest.Budget

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **The weights of `main`'s callees at `op`'s instructions**: the static ones' certificates,
the claim lists and `da_verify` by their trees' shapes (`Budget.clW_le`, `Budget.dvW_le`). -/
noncomputable def mainCounts (op : Opcode) :
    Budget.MainCounts (B2C.ωArm B2C.xmssArmC op) B2C.fs where
  kExp := kcExp op
  exp := kcExp_weightLe op
  kSd := kcSd op
  sd := kcSd_weightLe op
  kL1 := kcL1 op
  l1 := kcL1_loop op
  kL2 := kcL2 op
  l2 := kcL2_loop op
  kL3 := kcL3 op
  l3 := kcL3_loop op
  kL4 := kcL4 op
  l4 := kcL4_loop op
  aggC := kcAggC op
  aggD := kcAggD op
  agg := kcAgg_le op
  clA := kcClA op
  clS := kcClS op
  cl := fun _ _ _ _ n _ hv hb hT hn =>
    (Budget.cl_weight_le op hn hT hv hb).trans (Budget.clW_le op n)
  dvA := kcDvA op
  dvR := kcDvR op
  dvP := kcDvP op
  dv := fun _ _ _ _ r L _ hv hb hT h1 hr hL => by
    obtain ⟨hlo, hhi⟩ := B1.Da.nPad_bounds h1
    rw [← hL] at hlo hhi
    have hm : r ≤ 1024 := hr
    have hL11 : L < 11 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by omega : 2 ^ L < 2 ^ 11)
    exact (Budget.dv_weight_le op (by omega) hm hlo hL11 hT hv hb).trans
      (Budget.dvW_le op hlo hL11)

end
end LeanVM.Guest.Count
