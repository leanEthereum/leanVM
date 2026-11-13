/-
  LeanVM.Guest.B1.VerifySub.H.Keccak

  An honest child's Keccak reduction as `verify_keccak` takes it: the output lanes of
  `verify_tables`' claims, the reduction's run from `verify_tables`' last sponge, one committed
  outputs' claim on `q_keccak`.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermCtx
public import LeanVM.Guest.B1.KeccakGkr.VkCI

/-!
# The Keccak reduction

`lanes_slice`: claims on `claimColumns` have their output lanes at positions `105 .. 129`.
`ChildSegs.lanes`: on an honest child the lanes are twenty-five, on `keccakOutputColumns`, at
`chi` cut to the `KECCAK` table's height `τ`, their values the tables' evaluations `101 .. 125`.
`ChildSegs.keccak_run`: the Keccak phase's run is `verifyKeccak τ (chi.take τ) outs` from
`verify_tables`' last capacity, returning one claim `S.kOut` on `q_keccak`; the opened claims are
the lanes' complement and `S.kOut`. `ChildSegs.keccak_facts`: the bounds and lengths
`verify_keccak`'s completeness (`VkCompleteAtBK`) and the terminal take.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem claimColumns_pre : ∀ x ∈ Tables.claimColumns.take 105, x ∉ keccakOutputColumns := by
  decide +kernel

theorem claimColumns_mid : ∀ x ∈ (Tables.claimColumns.drop 105).take 25, x ∈ keccakOutputColumns := by
  decide +kernel

theorem claimColumns_post : ∀ x ∈ (Tables.claimColumns.drop 105).drop 25,
    x ∉ keccakOutputColumns := by
  decide +kernel

theorem claimColumns_lanes : (Tables.claimColumns.drop 105).take 25 = keccakOutputColumns := by
  decide +kernel

theorem claimColumns_length : Tables.claimColumns.length = 159 := by decide +kernel

/-- **The output lanes are claims `105 .. 129`.** -/
theorem lanes_slice {l : List ColumnClaim} (h : l.map (·.column) = Tables.claimColumns) :
    lanesOf l = (l.drop 105).take 25 := by
  have e : l = l.take 105 ++ ((l.drop 105).take 25 ++ (l.drop 105).drop 25) := by
    rw [List.take_append_drop, List.take_append_drop]
  unfold lanesOf
  conv_lhs => rw [e]
  rw [List.filter_append, List.filter_append]
  have h1 : (l.take 105).filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    have := claimColumns_pre _ (by rw [← h, ← List.map_take]; exact List.mem_map_of_mem hc)
    simpa using this
  have h2 : ((l.drop 105).take 25).filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) =
      (l.drop 105).take 25 := by
    rw [List.filter_eq_self]
    intro c hc
    have := claimColumns_mid _ (by
      rw [← h, ← List.map_drop, ← List.map_take]; exact List.mem_map_of_mem hc)
    simpa using this
  have h3 : ((l.drop 105).drop 25).filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) =
      [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    have := claimColumns_post _ (by
      rw [← h, ← List.map_drop, ← List.map_drop]; exact List.mem_map_of_mem hc)
    simpa using this
  rw [h1, h2, h3]
  simp

theorem vsEvTab_lanes : ∀ i < 25, Tables.vsEvTab (101 + i) = 5 := by decide +kernel

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem τ_eq : S.τ = Tables.vtHt S.rowsN 5 := by
  show S.layout.tableLogHeights.getD opKeccak 0 = _
  rw [S.hlayout]
  rfl

/-- **The honest output lanes**: twenty-five, on `keccakOutputColumns`, at `chi` cut to `τ`, their
values the tables' evaluations `101 .. 125`. -/
theorem lanes (hbl : bytecode.length = 2 ^ 23) :
    (lanesOf S.claims).length = 25 ∧ (lanesOf S.claims).map (·.column) = keccakOutputColumns ∧
      (∀ c ∈ lanesOf S.claims, c.point = S.H.chiW.take S.τ) ∧
      S.outs = (S.H.evsT.flatten.drop 101).take 25 := by
  obtain ⟨h, -, -, -⟩ := S.H_run hbl
  have hr : S.H.rows.length = 6 := S.hrowsL
  have hcol : S.claims.map (·.column) = Tables.claimColumns := Tables.VtHonest.vtH_columns h hr
  have hl : S.claims.length = 159 := by
    rw [← List.length_map (f := (·.column)), hcol, claimColumns_length]
  have hs := lanes_slice hcol
  have hev : S.H.evsT.flatten.length = 153 := by
    have := (S.H_run hbl).2.2.2
    rw [(S.H_run hbl).2.1] at this
    simp only [Tables.VtHonest.curW, List.length_append, h.hx4, h.hbcW, h.hxR] at this
    have hn : S.H.n = S.nT := rfl
    omega
  refine ⟨by rw [hs]; simp [hl], by rw [hs, List.map_take, List.map_drop, hcol, claimColumns_lanes],
    fun c hc ↦ ?_, ?_⟩
  · rw [hs] at hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    simp only [List.length_take, List.length_drop, hl] at hj
    have hj25 : j < 25 := by omega
    simp only [List.getElem_take, List.getElem_drop]
    have hp := Tables.VtHonest.vtH_points h hr hbl
    have e := congrArg (fun l ↦ l[105 + j]?) hp
    simp only [List.getElem?_map,
      List.getElem?_eq_getElem (show 105 + j < S.H.claims.length by
        show 105 + j < S.claims.length; omega), Option.map_some] at e
    rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)] at e
    simp only [List.length_replicate, List.length_cons, List.length_nil, List.getElem?_map,
      List.getElem?_range (show 105 + j - 3 - 1 < 153 by omega), Option.map_some,
      Option.some.injEq] at e
    rw [show 105 + j - 3 - 1 = 101 + j by omega, vsEvTab_lanes j hj25] at e
    rw [S.τ_eq]
    exact e
  · show (lanesOf S.claims).map (·.value) = _
    rw [hs, List.map_take, List.map_drop]
    have hv := Tables.VtHonest.vtH_values h
    have hv' : S.claims.map (·.value) = S.H.xs4 ++ S.H.evsT.flatten ++ S.H.pcW := hv
    rw [hv', List.append_assoc, List.drop_append,
      List.drop_eq_nil_of_le (by simp [h.hx4]), List.nil_append, h.hx4,
      List.drop_append_of_le_length (by rw [hev]; omega),
      List.take_append_of_le_length (by simp [hev])]

/-- `chi` has one challenge per round of the table sumcheck. -/
theorem chiW_length : S.H.chiW.length = S.nT := Tables.VtHonest.chiW_length _

/-- The slot point has four coordinates. -/
theorem slots_length : S.H.slots.length = 4 := by
  simp [Tables.VtHonest.slots, Tables.bcSlots, busBits]

/-- **The output lanes' values in the stream**: words `101 .. 125` of the tables' evaluations,
past the four framework words, the share's ten and the sumcheck's `3 nT`. -/
theorem outs_stream (hbl : bytecode.length = 2 ^ 23) :
    S.outs = (S.xsT.drop (14 + 3 * S.nT + 101)).take 25 ∧
      S.xsT.length = 14 + 3 * S.nT + 153 := by
  obtain ⟨h, hcur, -, hlen⟩ := S.H_run hbl
  have hn : S.H.n = S.nT := rfl
  have hpre : (S.H.xs4 ++ S.H.bcW ++ S.H.xsR).length = 14 + 3 * S.nT := by
    simp only [List.length_append, h.hx4, h.hbcW, h.hxR, hn]
  have hd : S.xsT.drop (14 + 3 * S.nT) = S.H.evsT.flatten := by
    rw [hcur]
    exact List.drop_left' hpre
  refine ⟨?_, hlen⟩
  rw [(S.lanes hbl).2.2.2, ← List.drop_drop, hd]

/-- **The Keccak phase's run**: `verifyKeccak τ (chi.take τ) outs` from `verify_tables`' last
capacity, one claim `S.kOut` on `q_keccak`; the opened claims are the lanes' complement and
`S.kOut`. -/
theorem keccak_run (hbl : bytecode.length = 2 ^ 23) :
    S.kc.1 = S.claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ [S.kOut] ∧
      S.kOut = ⟨qkeccak, S.kOut.point, S.kOut.value⟩ ∧
      RunsTo (verifyKeccak S.τ (S.H.chiW.take S.τ) S.outs) ⟨S.H.s3.squeeze.2.cap, []⟩ S.xsK
        ([⟨qkeccak, S.kOut.point, S.kOut.value⟩], S.kc.2.1, S.kc.2.2) S.s6 := by
  obtain ⟨-, -, h5⟩ := S.H_spec hbl
  obtain ⟨hl25, -, hpt, -⟩ := S.lanes hbl
  have c5 : ∃ sp, (⟨S.H.s3.squeeze.2.cap, []⟩ : Fs).Carries sp := by rw [← h5]; exact S.c5
  have hrun : RunsTo (keccakPhaseClaims S.layout S.claims) ⟨S.H.s3.squeeze.2.cap, []⟩ S.xsK S.kc
      S.s6 := by rw [← h5]; exact S.runK
  unfold keccakPhaseClaims at hrun
  obtain ⟨u, xs1, xs2, t1, g1, hx, r1, k1⟩ := Tables.RunsG.unbind (Tables.RunsTo.toG hrun) c5
  obtain ⟨-, rfl, rfl, rfl⟩ := Tables.runsG_require_inv' r1 c5
  obtain ⟨⟨outputs, point, slices⟩, xs3, xs4, t2, g2, hx2, r2, k2⟩ := Tables.RunsG.unbind k1 c5
  dsimp only at k2
  obtain ⟨hk, rfl, rfl, rfl⟩ := Tables.RunsG.ret_inv k2 (Tables.RunsG.carries r2 c5)
  -- the result's shape
  have hshape : ∃ op word, outputs = [⟨qkeccak, op, word⟩] := by
    obtain ⟨sp, hsp⟩ := c5
    obtain ⟨sp', -, e⟩ := r2 sp hsp [] [] []
    have hr := VerifierProgram.returns_of_run keccak256 keccakF1600 e
    rw [verifyKeccak_eq] at hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
    have := VerifierProgram.returns_ret hr
    simp only [Prod.mk.injEq] at this
    exact ⟨_, _, this.1⟩
  obtain ⟨op, word, rfl⟩ := hshape
  have hkc : S.kc = (S.claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++
      [⟨qkeccak, op, word⟩], point, slices) := hk
  have hkO : S.kOut = ⟨qkeccak, op, word⟩ := by
    show S.kc.1.getLastD default = _
    rw [hkc]
    simp
  -- the lanes' point
  obtain ⟨a, l', hal⟩ : ∃ a l', lanesOf S.claims = a :: l' := by
    cases hh : lanesOf S.claims with
    | nil => rw [hh] at hl25; simp at hl25
    | cons a l' => exact ⟨a, l', rfl⟩
  have hp0 : ((lanesOf S.claims).headD default).point = S.H.chiW.take S.τ := by
    rw [hal]; exact hpt a (by rw [hal]; exact List.mem_cons_self)
  refine ⟨by rw [hkc, hkO], by rw [hkO], ?_⟩
  rw [hkO, hkc]
  have hτ : S.layout.tableLogHeights.getD opKeccak 0 = S.τ := rfl
  rw [hx, hx2, List.nil_append, List.append_nil, ← hp0]
  exact r2

/-- **The Keccak reduction's bounds and lengths.** -/
theorem keccak_facts (hbl : bytecode.length = 2 ^ 23) :
    9 ≤ S.τ ∧ S.τ ≤ 24 ∧ S.τ ≤ S.H.chiW.length ∧ S.outs.length = 25 ∧
      S.H.s3.squeeze.2.cap.length = 5 ∧ S.kOut.point.length = S.τ + 6 ∧
      S.kc.2.1.length = S.τ + 6 ∧ S.kc.2.2.length = 64 := by
  have h22 := (S.hs_bounds hbl).2
  have hτ : S.τ = S.hs.getD 5 0 := S.τ_eq
  have h9 : 9 ≤ S.τ := by
    rw [S.τ_eq, Tables.vtHt_eq S.hrowsL (by norm_num)]
    exact le_max_of_le_right (by decide)
  have hn : S.τ ≤ S.H.chiW.length := by
    rw [Tables.VtHonest.chiW_length, S.τ_eq]
    exact Tables.vt_n_ge (H := S.H) S.hrowsL (t := 5) (by norm_num)
  have ho : S.outs.length = 25 := by
    show ((lanesOf S.claims).map (·.value)).length = 25
    rw [List.length_map]; exact (S.lanes hbl).1
  have hf : S.H.s3.squeeze.2.cap.length = 5 := by simp [Fs.squeeze, capOf]
  obtain ⟨-, -, hrun⟩ := S.keccak_run hbl
  obtain ⟨D, hDτ, -, -, -, -, hDs, hD, -, hop, hpt, -⟩ := vkData_of_run h9 (by omega) hn ho hf
    (by rw [← (S.H_spec hbl).2.2]; exact S.c5) hrun
  refine ⟨h9, by omega, hn, ho, hf, ?_, ?_, ?_⟩
  · rw [← hop, VkData.op_length hD, hDτ]
  · rw [← hpt, VkData.point_length hD, hDτ]
  · obtain ⟨-, -, -, -, -, -, -, -, -, hsl, -⟩ := hD
    rw [← hDs]
    exact hsl

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
