/-
  LeanVM.Guest.B2C.ShareLink

  A compiled function passes the sharing check (`ShareOk`) when its local sharing check holds on
  its data.
-/

module

public import LeanVM.Guest.B2C.ShareLStatic
public import LeanVM.Guest.B2C.ShareChecked

/-!
# The sharing check of a compiled function

`shareOk_of_checked`: function `j`'s core IR, certificate, completeness data and frame size are
the data a local sharing check holds on (`ShareChecked`), so `ShareOk j`: its path conclusion
(`ShareL.path_of_check`), its static facts (`ShareL.staticD_of_check`), and from them and the
certificate's lists its cells apart (`Apart`) and its temporaries and runs listed (`FnStatic`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-- The cells apart, from the check's lists and its free cells. -/
theorem apart_of_static {j : ℕ} {cf : Core.Fn} {fs : ℕ} {main : Bool} {mc : ℕ}
    (hm : Nat.beq j 1 = main) (hmc : main = true → Data.mainCells = mc)
    (hS : ShareL.StaticD cf (certOf j) (plumbOf j) fs main mc) : Apart j := by
  have h := hS.apartL
  unfold ShareL.apartOkL at h
  simp only [natSeq_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, h4⟩, h5⟩, h6⟩, h8⟩, h7⟩ := h
  have tc : ∀ p ∈ (plumbOf j).tmps, (tmpCells (plumbOf j)).testBit p.2 = true := fun p hp ↦
    mem_bitsOf (List.mem_map_of_mem hp)
  have rc : ∀ p ∈ (plumbOf j).runs, (bitsOf ((plumbOf j).runs.map Prod.snd)).testBit p.2 = true :=
    fun p hp ↦ mem_bitsOf (List.mem_map_of_mem hp)
  have stc : ∀ q ∈ (plumbOf j).stat, (bitsOf ((plumbOf j).stat.map Prod.fst)).testBit q.1 = true :=
    fun q hq ↦ mem_bitsOf (List.mem_map_of_mem hq)
  have scc : ∀ c ∈ siteCells (plumbOf j), (bitsOf (siteCells (plumbOf j))).testBit c = true :=
    fun c hc ↦ mem_bitsOf hc
  have acc : ∀ a ∈ (plumbOf j).arms, (bitsOf ((plumbOf j).arms.map fun a ↦ a.2.1)).testBit a.2.1 = true :=
    fun a ha ↦ mem_bitsOf (List.mem_map_of_mem (f := fun a : ℕ × ℕ × ℕ ↦ a.2.1) ha)
  refine ⟨fun q hq p hp he ↦ ?_, fun c hc ↦ ?_, fun a ha ↦ ?_, (bitsNodup_spec _ _ h4).1,
    (bitsNodup_spec _ _ h5).1, (bitsNodup_spec _ _ h6).1, fun p hp ↦ ?_, fun hj ↦ ?_⟩
  · have := apart_spec ha (stc q hq)
    rw [← he, tc p hp] at this; cases this
  · have hs := apart_spec hb (scc c hc)
    simp only [testBit_lor', Bool.or_eq_false_iff] at hs
    obtain ⟨⟨ht, hr⟩, hst⟩ := hs
    refine ⟨fun p hp he ↦ ?_, fun p hp he ↦ ?_, fun q hq he ↦ ?_, hS.sites c hc⟩
    · rw [← he, tc p hp] at ht; cases ht
    · rw [← he, rc p hp] at hr; cases hr
    · rw [← he, stc q hq] at hst; cases hst
  · have hs := apart_spec hc (acc a ha)
    simp only [testBit_lor', Bool.or_eq_false_iff] at hs
    obtain ⟨⟨⟨ht, hr⟩, hst⟩, hsc⟩ := hs
    refine ⟨fun p hp he ↦ ?_, fun p hp he ↦ ?_, fun q hq he ↦ ?_, hS.arms a ha, fun hl ↦ ?_⟩
    · rw [← he, tc p hp] at ht; cases ht
    · rw [← he, rc p hp] at hr; cases hr
    · rw [← he, stc q hq] at hst; cases hst
    · rw [scc _ hl] at hsc; cases hsc
  · simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, nbeq_iff, beq_iff_eq] at h8
    obtain ⟨q, hq, h1, h2⟩ := h8 p hp
    rw [← h1, ← h2]; exact hq
  · subst hj
    have hmain : main = true := by rw [← hm]; rfl
    subst hmain
    rw [← hmc rfl] at h7 hS
    simp only [Bool.cond_true, Nat.blt_eq] at h7
    have hlt : ∀ c, (Nat.lor (Nat.lor (Nat.lor (tmpCells (plumbOf 1)) (bitsOf ((plumbOf 1).runs.map Prod.snd)))
        (bitsOf ((plumbOf 1).stat.map Prod.fst))) (Nat.lor (bitsOf (siteCells (plumbOf 1)))
          (bitsOf ((plumbOf 1).arms.map fun a ↦ a.2.1)))).testBit c = true → c < Data.mainCells :=
      fun c hc ↦ lt_of_testBit_lt h7 hc
    refine ⟨fun p hp ↦ hlt _ ?_, fun p hp ↦ hlt _ ?_, fun q hq ↦ hlt _ ?_,
      fun c hc ↦ hS.mainBound rfl c hc, fun c hc ↦ hlt _ ?_, fun a ha ↦ hlt _ ?_⟩
    · exact testBit_lor_l (testBit_lor_l (testBit_lor_l (tc p hp)))
    · exact testBit_lor_l (testBit_lor_l (testBit_lor_r (rc p hp)))
    · exact testBit_lor_l (testBit_lor_r (stc q hq))
    · exact testBit_lor_r (testBit_lor_l (scc c hc))
    · exact testBit_lor_r (testBit_lor_r (acc a ha))

/-- **A function's sharing check from its local check**, over its data. -/
theorem shareOk_of_checked {j : ℕ} (hc : ShareChecked j) : ShareOk j := by
  obtain ⟨G, f, cf, C, main, mc, T, h, hm, hmc, ok⟩ := hc
  have H := ShareL.checkL_spec ok
  have hS := ShareL.staticD_of_check H
  rw [← h.core, ← h.cert] at H hS
  have hlists := hS.lists
  simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
  obtain ⟨⟨⟨⟨⟨-, ht⟩, hr⟩, hrt⟩, -⟩, -⟩ := hlists
  obtain ⟨htIn, htFun⟩ := pairsOk_spec ht
  obtain ⟨hrIn, hrFun⟩ := pairsOk_spec hr
  refine ⟨fun hw he ↦ ShareL.path_of_check H hw he, fun v hv ↦ hS.vals v hv, fun v hv ↦ hS.param v hv,
    ⟨fun t ht' ↦ hS.tmp t ht', htIn, htFun, fun p r rs ha k hk ↦ hS.run p r rs ha k hk, hrIn, hrFun,
      fun p hp q hq he ↦ ?_⟩, apart_of_static hm hmc hS, hS.lists⟩
  have := hrt p hp
  simp only [Bool.not_eq_true', bitN_eq, tmpCells] at this
  have hin : (bitsOf ((plumbOf j).tmps.map Prod.snd)).testBit p.2 = true :=
    (testBit_bitsOf _ _).mpr (List.mem_map.mpr ⟨q, hq, he⟩)
  rw [this] at hin; cases hin

end
end LeanVM.Guest.B2C
