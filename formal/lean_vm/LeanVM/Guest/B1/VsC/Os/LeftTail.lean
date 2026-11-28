/-
  LeanVM.Guest.B1.VsC.Os.LeftTail

  `open_stacked`'s callees after its levels, placed in order at the node's valuation.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftRes

/-!
# The tail's callees

After the levels, `open_stacked` calls `opening_tail_round` `yrLog` times, `fold_final_msg__L{yrLog}`,
`is_zero` per non-final level, then per non-final level `level_residual`, `is_zero`,
`level_residual_slow` (`osTailSpec`). Nothing after them is a frame address in the node's words, so
their ends need no choice: `kidsAtF_quiet` places callees that each complete at every cursor, quiet,
claiming nothing. `osFfm` (one kernel decision): the final message's fold is deployed.
`HonRun.kidsAtF_tail`: the tail's calls complete in order from any cursor.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Every arm's final message fold is deployed. -/
def OsFfmOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri =>
    decide (("fold_final_msg__L" ++ natStr (osCfgR m ri).yrLog, (osCfgR m ri).yrLog) ∈ foldFinalMsgNames)

set_option maxRecDepth 100000 in
theorem osFfmOk_all : (List.range 15).all OsFfmOk = true := by decide +kernel

theorem osFfm {m ri : ℕ} (hm : m < 15) (hri : ri < 4) :
    ("fold_final_msg__L" ++ natStr (osCfgR m ri).yrLog, (osCfgR m ri).yrLog) ∈ foldFinalMsgNames := by
  have h := List.all_eq_true.mp osFfmOk_all m (List.mem_range.mpr hm)
  simp only [OsFfmOk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h ri hri

theorem forall₂_mem_left {α β : Type _} {P : α → β → Prop} {Q : α → Prop} :
    ∀ {cs : List α} {ss : List β}, List.Forall₂ P cs ss → (∀ c s, c ∈ cs → s ∈ ss → P c s → Q c) → ∀ c ∈ cs, Q c
  | [], [], .nil, _ => fun _ h => absurd h List.not_mem_nil
  | _ :: _, _ :: _, .cons h1 h2, h => fun c hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h _ _ List.mem_cons_self List.mem_cons_self h1
    · exact forall₂_mem_left h2
        (fun c s hc' hs hp => h c s (List.mem_cons_of_mem _ hc') (List.mem_cons_of_mem _ hs) hp) c hc

section
variable {al : String → Bool} {k : ℕ} {σ : Val} {Rn : ℕ → Prop} {Pre : Reader → Prop}

/-- **Callees each completing quiet at every cursor, claiming nothing**, in order from any cursor. -/
theorem kidsAtF_quiet {P : Reader → Prop} {O : Reader → Prop} {Dacc : ℕ → Prop} (hP : ∀ rd, Pre rd → O rd → P rd) :
    ∀ (cs : List Call) (cur : ℕ), (∀ c ∈ cs, c.taken = true ∧ ∀ cur', ∃ (B ec : ℕ) (Rc : ℕ → Prop),
      (∀ i, Rc i → Rn i) ∧ CallAtA B2C.fs al B2C.cert k c.f (c.args.map σ) (c.rets.map σ) Rc (fun _ => False)
        (fun _ => True) P PostQuiet B (allocBase (al c.f) cur') (allocBase (al c.f) cur' + B) ec) →
      ∃ e, KidsAtF B2C.fs al B2C.cert k σ Rn Pre O Dacc (cs.map fun _ => PostQuiet) cs cur e O Dacc
  | [], cur, _ => ⟨cur, kidsAtF_nilStep (fun _ h => h) (fun _ h => h)⟩
  | c :: cs, cur, h => by
    obtain ⟨ht, hc⟩ := h c List.mem_cons_self
    obtain ⟨B, ec, Rc, hRc, hca⟩ := hc cur
    obtain ⟨e, he⟩ := kidsAtF_quiet hP cs ec fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    exact ⟨e, kidsAtF_callStep ht rfl rfl hca (fun i hi => Or.inl (hRc i hi)) hP
      (kidsAtF_mono _ _ _ _ _ _ _ _ _ _ he (fun _ h => h.1) (fun _ h => Or.inl h))⟩

/-- A leaf's obligation in `kidsAtF_quiet`. -/
theorem quiet_of_leaf {c : Call} {S : ℕ → Prop} {P : Reader → Prop} (hS : ∀ i, S i → Rn i)
    (hL : LeafAtA B2C.fs al B2C.cert k c.f (c.args.map σ) (c.rets.map σ) S (fun _ => True) P PostQuiet) :
    ∀ cur', ∃ (B ec : ℕ) (Rc : ℕ → Prop),
      (∀ i, Rc i → Rn i) ∧ CallAtA B2C.fs al B2C.cert k c.f (c.args.map σ) (c.rets.map σ) Rc (fun _ => False)
        (fun _ => True) P PostQuiet B (allocBase (al c.f) cur') (allocBase (al c.f) cur' + B) ec :=
  fun cur' => ⟨_, _, S, hS, hL (allocBase (al c.f) cur') _ le_rfl⟩

theorem p16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
theorem p28 : (2 : ℕ) ^ 28 = 268435456 := by norm_num

/-- **`kidsAtF_quiet` with the end bounded**: each callee within `β` of its cursor when `P0` holds. -/
theorem kidsAtF_quietB {P : Reader → Prop} {O : Reader → Prop} {Dacc : ℕ → Prop} {P0 : Prop} {β : ℕ}
    (hP : ∀ rd, Pre rd → O rd → P rd) :
    ∀ (cs : List Call) (cur : ℕ), (∀ c ∈ cs, c.taken = true ∧ ∀ cur', ∃ (B ec : ℕ) (Rc : ℕ → Prop),
      (P0 → ec ≤ cur' + β) ∧ (∀ i, Rc i → Rn i) ∧ CallAtA B2C.fs al B2C.cert k c.f (c.args.map σ) (c.rets.map σ) Rc
        (fun _ => False) (fun _ => True) P PostQuiet B (allocBase (al c.f) cur') (allocBase (al c.f) cur' + B) ec) →
      ∃ e, (P0 → e ≤ cur + cs.length * β) ∧
        KidsAtF B2C.fs al B2C.cert k σ Rn Pre O Dacc (cs.map fun _ => PostQuiet) cs cur e O Dacc
  | [], cur, _ => ⟨cur, fun _ => by simp, kidsAtF_nilStep (fun _ h => h) (fun _ h => h)⟩
  | c :: cs, cur, h => by
    obtain ⟨ht, hc⟩ := h c List.mem_cons_self
    obtain ⟨B, ec, Rc, hb, hRc, hca⟩ := hc cur
    obtain ⟨e, hbe, he⟩ := kidsAtF_quietB hP cs ec fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    refine ⟨e, fun h0 => ?_, kidsAtF_callStep ht rfl rfl hca (fun i hi => Or.inl (hRc i hi)) hP
      (kidsAtF_mono _ _ _ _ _ _ _ _ _ _ he (fun _ h => h.1) (fun _ h => Or.inl h))⟩
    have h1 := hb h0
    have h2 := hbe h0
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- A leaf's obligation in `kidsAtF_quietB`. -/
theorem quiet_of_leafB {c : Call} {S : ℕ → Prop} {P : Reader → Prop} {P0 : Prop} {β : ℕ} (hS : ∀ i, S i → Rn i)
    (hβ : P0 → B2C.fs c.f + 15 ≤ β)
    (hL : LeafAtA B2C.fs al B2C.cert k c.f (c.args.map σ) (c.rets.map σ) S (fun _ => True) P PostQuiet) :
    ∀ cur', ∃ (B ec : ℕ) (Rc : ℕ → Prop), (P0 → ec ≤ cur' + β) ∧
      (∀ i, Rc i → Rn i) ∧ CallAtA B2C.fs al B2C.cert k c.f (c.args.map σ) (c.rets.map σ) Rc (fun _ => False)
        (fun _ => True) P PostQuiet B (allocBase (al c.f) cur') (allocBase (al c.f) cur' + B) ec :=
  fun cur' => ⟨_, _, S, fun h0 => by have := hβ h0; have := allocBase_le (al c.f) cur'; omega, hS,
    hL (allocBase (al c.f) cur') _ le_rfl⟩

end

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

set_option hygiene false in
local notation "CC" => osCfgR (μ - minOpenLog) (r - 1)

set_option hygiene false in
local notation "HH" => hR.osHonest (cur := cur) (tabs := tabs)

/-- **The tail's callees complete in order** from any cursor, at the node's valuation. -/
theorem kidsAtF_tail {cur tabs : E} (al : String → Bool) (k : ℕ) (σ0 : Val) (rd0 : Reader) (b : ℕ)
    (Rn Sc : ℕ → Prop) (Pre : Reader → Prop) (hRb : ∀ i, osBufCells CC b i → Rn i) (hRS : ∀ i, Sc i → Rn i)
    (hPre : ∀ rd, Pre rd → ReadsAt rd cur xs ∧ WinTabs rd tabs) (O : Reader → Prop) (Dacc : ℕ → Prop)
    (hO : ∀ rd, O rd → OsMemA rd CC b (HH).own)
    (hv : OsHelperVals CC b tabs (HH).own (HH).D σ0)
    (h0 : OsNF CC b (HH).own cur tabs xs rd0) (hS0 : OsNF CC b (HH).own cur tabs xs (restrict rd0 Sc))
    {cs : List Call} (hcs : List.Forall₂ (fun c s => callMatches c s = true) cs (osTailSpec CC))
    (hcall : ∀ c ∈ cs, osCmin CC b (HH).own cur tabs xs rd0 c.f (c.args.map σ0) (c.rets.map σ0)) (cur0 : ℕ) :
    ∃ e, KidsAtF B2C.fs al B2C.cert k σ0 Rn Pre O Dacc (cs.map fun _ => PostQuiet) cs cur0 e O Dacc := by
  have hm := hR.m11
  have hr := hR.r4
  have hy := hR.yr
  refine kidsAtF_quiet (P := OsNF CC b (HH).own cur tabs xs)
    (fun rd hp ho => ⟨(hPre rd hp).1, (hPre rd hp).2, hO rd ho⟩) cs cur0 ?_
  have hRb' : ∀ j < (osSizesL CC).length, ∀ i < (osSizesL CC).getD j 0, osBufCells CC b
      ((bases b (osSizesL CC)).getD j 0 + i) := fun j hj i hi => osBufCells_of hj hi
  refine forall₂_mem_left hcs fun c s hc hs hcm => ?_
  simp only [osTailSpec, List.mem_append, List.mem_replicate, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((⟨-, rfl⟩ | rfl) | ⟨-, rfl⟩) | ⟨l, hlt, rfl | rfl | rfl⟩
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    obtain ⟨hpre, hfx⟩ := hcall c hc .tail (by rw [hf]; exact osKindOf_tail)
    refine ⟨ht, quiet_of_leaf hRS ?_⟩
    rw [hf]
    exact osLeaf_tail (fs := B2C.fs) (al := al) (cert := B2C.cert) k hpre hfx h0 hS0
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    have hp := osFfm hm hr
    obtain ⟨hpre, hfx⟩ := hcall c hc (.ffm (CC).yrLog) (by rw [hf]; exact osKindOf_ffm hp)
    refine ⟨ht, quiet_of_leaf hRS ?_⟩
    rw [hf]
    exact osLeaf_ffm (fs := B2C.fs) (al := al) (cert := B2C.cert) k hp hpre hfx h0 hS0
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    obtain ⟨hpre, -⟩ := hcall c hc .iz (by rw [hf]; exact osKindOf_isZero)
    refine ⟨ht, quiet_of_leaf hRS ?_⟩
    rw [hf]
    exact osLeaf_iz (fs := B2C.fs) (al := al) (cert := B2C.cert) (S := Sc) k hpre _
  · have hc' := callMatches_some hcm
    subst hc'
    have hl' : l < (CC).levels.length := by omega
    obtain ⟨ha, hrt, -, -⟩ := (hv l hl').2.2.2.2 hlt
    refine ⟨rfl, fun cur' => ?_⟩
    obtain ⟨e, -, he⟩ := osLrEntry (al := al) (k := k) hm hr hlt b (HH).own_len ((HH).D l).mu (osBufCells CC b) hRb'
      (allocBase (al (osResidualName (osLvA CC l))) cur') _ le_rfl
    rw [← ha, ← hrt] at he
    exact ⟨_, e, osBufCells CC b, hRb, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.2.2) (fun _ _ _ h => h)⟩
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    obtain ⟨hpre, -⟩ := hcall c hc .iz (by rw [hf]; exact osKindOf_isZero)
    refine ⟨ht, quiet_of_leaf hRS ?_⟩
    rw [hf]
    exact osLeaf_iz (fs := B2C.fs) (al := al) (cert := B2C.cert) (S := Sc) k hpre _
  · have hc' := callMatches_some hcm
    subst hc'
    have hl' : l < (CC).levels.length := by omega
    obtain ⟨-, -, ha, hrt⟩ := (hv l hl').2.2.2.2 hlt
    refine ⟨rfl, fun cur' => ?_⟩
    obtain ⟨e, -, he⟩ := osLrsEntry (al := al) (k := k) hm hr hlt b (HH).own_len ((HH).D l).lam (osBufCells CC b)
      hRb' (allocBase (al (osSlowName CC (osLvA CC l))) cur') _ le_rfl
    rw [← ha, ← hrt] at he
    exact ⟨_, e, osBufCells CC b, hRb, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.2.2) (fun _ _ _ h => h)⟩


/-- **The tail's callees complete in order, their end bounded**, every frame at most `2^16` and every
level's queries at most `2^10`. -/
theorem kidsAtF_tailB {cur tabs : E} (al : String → Bool) (k : ℕ) (σ0 : Val) (rd0 : Reader) (b : ℕ)
    (Rn Sc : ℕ → Prop) (Pre : Reader → Prop) (hRb : ∀ i, osBufCells CC b i → Rn i) (hRS : ∀ i, Sc i → Rn i)
    (hPre : ∀ rd, Pre rd → ReadsAt rd cur xs ∧ WinTabs rd tabs) (O : Reader → Prop) (Dacc : ℕ → Prop)
    (hO : ∀ rd, O rd → OsMemA rd CC b (HH).own)
    (hv : OsHelperVals CC b tabs (HH).own (HH).D σ0)
    (h0 : OsNF CC b (HH).own cur tabs xs rd0) (hS0 : OsNF CC b (HH).own cur tabs xs (restrict rd0 Sc))
    {cs : List Call} (hcs : List.Forall₂ (fun c s => callMatches c s = true) cs (osTailSpec CC))
    (hcall : ∀ c ∈ cs, osCmin CC b (HH).own cur tabs xs rd0 c.f (c.args.map σ0) (c.rets.map σ0)) (cur0 : ℕ)
    (hQ : ∀ l < (CC).yrLevel, (osLvA CC l).queries ≤ 2 ^ 10) :
    ∃ e, ((∀ f, B2C.fs f ≤ 2 ^ 16) → e ≤ cur0 + cs.length * 2 ^ 28) ∧ KidsAtF B2C.fs al B2C.cert k σ0 Rn Pre O Dacc (cs.map fun _ => PostQuiet) cs cur0 e O Dacc := by
  have hm := hR.m11
  have hr := hR.r4
  have hy := hR.yr
  refine kidsAtF_quietB (P0 := ∀ f, B2C.fs f ≤ 2 ^ 16) (β := 2 ^ 28) (P := OsNF CC b (HH).own cur tabs xs)
    (fun rd hp ho => ⟨(hPre rd hp).1, (hPre rd hp).2, hO rd ho⟩) cs cur0 ?_
  have hRb' : ∀ j < (osSizesL CC).length, ∀ i < (osSizesL CC).getD j 0, osBufCells CC b
      ((bases b (osSizesL CC)).getD j 0 + i) := fun j hj i hi => osBufCells_of hj hi
  refine forall₂_mem_left hcs fun c s hc hs hcm => ?_
  simp only [osTailSpec, List.mem_append, List.mem_replicate, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((⟨-, rfl⟩ | rfl) | ⟨-, rfl⟩) | ⟨l, hlt, rfl | rfl | rfl⟩
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    obtain ⟨hpre, hfx⟩ := hcall c hc .tail (by rw [hf]; exact osKindOf_tail)
    refine ⟨ht, quiet_of_leafB hRS (fun h0 => by have := h0 c.f; have := p16; have := p28; omega) ?_⟩
    rw [hf]
    exact osLeaf_tail (fs := B2C.fs) (al := al) (cert := B2C.cert) k hpre hfx h0 hS0
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    have hp := osFfm hm hr
    obtain ⟨hpre, hfx⟩ := hcall c hc (.ffm (CC).yrLog) (by rw [hf]; exact osKindOf_ffm hp)
    refine ⟨ht, quiet_of_leafB hRS (fun h0 => by have := h0 c.f; have := p16; have := p28; omega) ?_⟩
    rw [hf]
    exact osLeaf_ffm (fs := B2C.fs) (al := al) (cert := B2C.cert) k hp hpre hfx h0 hS0
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    obtain ⟨hpre, -⟩ := hcall c hc .iz (by rw [hf]; exact osKindOf_isZero)
    refine ⟨ht, quiet_of_leafB hRS (fun h0 => by have := h0 c.f; have := p16; have := p28; omega) ?_⟩
    rw [hf]
    exact osLeaf_iz (fs := B2C.fs) (al := al) (cert := B2C.cert) (S := Sc) k hpre _
  · have hc' := callMatches_some hcm
    subst hc'
    have hl' : l < (CC).levels.length := by omega
    obtain ⟨ha, hrt, -, -⟩ := (hv l hl').2.2.2.2 hlt
    refine ⟨rfl, fun cur' => ?_⟩
    obtain ⟨e, hbe, he⟩ := osLrEntry (al := al) (k := k) hm hr hlt b (HH).own_len ((HH).D l).mu (osBufCells CC b) hRb'
      (allocBase (al (osResidualName (osLvA CC l))) cur') _ le_rfl
    rw [← ha, ← hrt] at he
    refine ⟨_, e, osBufCells CC b, fun h0 => ?_, hRb, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.2.2) (fun _ _ _ h => h)⟩
    have h1 := hbe (2 ^ 16) h0
    have h2 := allocBase_le (al (osResidualName (osLvA CC l))) cur'
    have h3 := h0 (osResidualName (osLvA CC l))
    have h5 : ((osLvA CC l).queries + 4) * (2 ^ 16 + 32) ≤ 1028 * 65568 :=
      Nat.mul_le_mul (by have := hQ l hlt; omega) (by norm_num)
    have := p16; have := p28
    omega
  · obtain ⟨hf, ht⟩ := callMatches_none hcm
    obtain ⟨hpre, -⟩ := hcall c hc .iz (by rw [hf]; exact osKindOf_isZero)
    refine ⟨ht, quiet_of_leafB hRS (fun h0 => by have := h0 c.f; have := p16; have := p28; omega) ?_⟩
    rw [hf]
    exact osLeaf_iz (fs := B2C.fs) (al := al) (cert := B2C.cert) (S := Sc) k hpre _
  · have hc' := callMatches_some hcm
    subst hc'
    have hl' : l < (CC).levels.length := by omega
    obtain ⟨-, -, ha, hrt⟩ := (hv l hl').2.2.2.2 hlt
    refine ⟨rfl, fun cur' => ?_⟩
    obtain ⟨e, hbe, he⟩ := osLrsEntry (al := al) (k := k) hm hr hlt b (HH).own_len ((HH).D l).lam (osBufCells CC b)
      hRb' (allocBase (al (osSlowName CC (osLvA CC l))) cur') _ le_rfl
    rw [← ha, ← hrt] at he
    refine ⟨_, e, osBufCells CC b, fun h0 => ?_, hRb, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.2.2) (fun _ _ _ h => h)⟩
    have h1 := hbe (2 ^ 16) h0
    have h2 := allocBase_le (al (osSlowName CC (osLvA CC l))) cur'
    have h3 := h0 (osSlowName CC (osLvA CC l))
    have h5 : ((osLvA CC l).queries + 3) * (2 * 2 ^ 16 + 32) ≤ 1027 * 131104 :=
      Nat.mul_le_mul (by have := hQ l hlt; omega) (by norm_num)
    have := p16; have := p28
    omega

end
end LeanVM.Guest.B1.Whir.HonRun
