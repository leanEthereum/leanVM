/-
  LeanVM.Guest.B1.VsC.VsNatHos

  `open_stacked`'s call at the honest context: the guest's arguments are the native verifier's, so the native call
  is `D3.Ok.hos`.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatOpenCtx
public import LeanVM.Guest.B1.VsC.VsNatRg
public import LeanVM.Guest.B1.VsC.VsNatFs
public import LeanVM.Guest.B1.VerifySub.PhOpenLib
public import LeanVM.Guest.B1.VerifySub.PhLinkEnd
public import LeanVM.Guest.B1.VerifySub.Chain

/-!
# `open_stacked`'s arguments, natively

`hos_nat`'s guest equalities at `x.σ0`:

* **`VsCtx.h96_nat`** (a): the rate's selector `.n 96 = g^(r - 1)` from `g_power_of_word`'s return.
* **`VsCtx.ring_nat`** (b): past the ring grind's permutation (`ring_cells`), the two permutations of its capacity
  (`vsC`'s `2552 ..< 2569`, kernel-checked) leave `ringCap S` at `.n 3033 … 3037`, `ringRho S` at `.n 3026`,
  `ringLam S` at `.n 3027` (`phRing`'s `hcap2`, read forwards).
* **`vsOpenTarget_eq`**, **`NatOpen.Ok.vals`** (c): the guest's Horner sum is the stacked opening's target once the
  native claims' values are the guest's, which are, natively, the merged ring claim's, `m1`, the message's first `55`
  words, the public input's two, the Keccak word, the out-of-domain value (`phOpen_of_ood`'s value analysis forwards).
* **`VsCtx.stream89_nat`** (d): `.n 134`, `.n 137` are the stream's words `8`, `9`.
* **`VsCtx.openCall_nat`** (e): the native call at `ic = bm + 144 + nx + 1`, its region the caller's or the buffers.
* **`VsCtx.hos_honest`** (f): the native call, at the honest choices, is `D3.Ok.hos`; `VsCtx.hQo_nat` its post.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## (a) The rate's selector -/

section
variable {x : VsCtx}

/-- **`.n 96`, natively**: `g^(r - 1)`, the rate's selector. -/
theorem VsCtx.h96_nat (hret : CausalRule x.ret) (hR : x.Ret1F) {layout : Layout} {r : ℕ}
    (hann : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, r)) (hr1 : 1 ≤ r) :
    x.σ0 (.n 96) = rateSel r := by
  have ha : x.args.length = 6 := rfl
  have hR' := hR
  unfold VsCtx.Ret1F at hR'
  rw [hann] at hR'
  have hw94 : x.w 94 = gen ^ r := (vsW_ret' ha hret (i := 94) (by decide)).trans (hR'.r94 _)
  have h94 : vsVal x.rd0 x.w x.args (.n 94) = gen ^ r :=
    (vsVal_call_ret ha vsW3_eq (.n 94) (List.mem_singleton_self _)).trans hw94
  have hg := vsW4_good (rd0 := x.rd0) (w := x.w) ha
  have h95 : vsVal x.rd0 x.w x.args (.n 95) = gen ^ 1 := by
    have := hg (.const (.n 95) (word 2 0)) (by simp [vsW4]); simp only [Good] at this
    rw [this]; exact wordG (j := 1) (by norm_num)
  have h96 : vsVal x.rd0 x.w x.args (.n 96) = gen ^ (r - 1) := by
    have := hg (.mul (.n 94) (.n 96) (.n 95)) (by simp [vsW4])
    simp only [Good, show ¬ ((V.n 96).idx < (V.n 94).idx ∧ (V.n 95).idx < (V.n 94).idx) from by decide,
      ↓reduceIte] at this
    rw [this, h94, h95, gen_div hr1]
  show vsVal x.rd0 x.w x.args (.n 96) = ofK (addressOfIndex (r - 1))
  rw [h96, LeanVM.Guest.Value.gen_pow_eq_ofK]

end

/-! ## (b) The ring switch's capacity and challenges -/

/-- Statements `2980 ..< 2998` (`vsC`'s `2552 ..< 2570`): the challenges' copies and the two permutations of the
capacity alone. -/
def vsRingRestA : List Atom :=
  [.copy (.n 2997) (.n 2930), .copy (.n 2998) (.n 2932), .copy (.n 2999) (.n 2933), .copy (.n 3000) (.n 2934),
    .copy (.n 3001) (.n 2935), .copy (.n 3002) (.n 2936), .copy (.n 3003) (.n 2937),
    .keccak [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2938, .n 2939, .n 2940, .n 2941, .n 2942]
      [.n 3004, .n 3005, .n 3006, .n 3007, .n 3008, .n 3009, .n 3010, .n 3011, .n 3012, .n 3013, .n 3014, .n 3015,
        .n 3016] false false,
    .copy (.n 3017) (.n 3004), .copy (.n 3018) (.n 3005), .copy (.n 3019) (.n 3006), .copy (.n 3020) (.n 3007),
    .copy (.n 3021) (.n 3008), .copy (.n 3022) (.n 3009), .copy (.n 3023) (.n 3010), .copy (.n 3024) (.n 3011),
    .keccak [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 3012, .n 3013, .n 3014, .n 3015, .n 3016]
      [.n 3025, .n 3026, .n 3027, .n 3028, .n 3029, .n 3030, .n 3031, .n 3032, .n 3033, .n 3034, .n 3035, .n 3036,
        .n 3037] false false,
    .copy (.n 3038) (.n 3025)]

set_option maxRecDepth 200000 in
theorem vsRingRestA_eq : (vsC.drop 2552).take 18 = vsRingRestA.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

/-- The draw's merging and batching challenges, by position. -/
theorem ringRho_eq (S : KeccakState) : ringRho S = Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S)))) 1 := by
  unfold ringRho ringChs
  rw [VerifySub.grindPacked_list]
  rfl

theorem ringLam_eq (S : KeccakState) : ringLam S = Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S)))) 2 := by
  unfold ringLam ringChs
  rw [VerifySub.grindPacked_list]
  rfl

section
variable {x : VsCtx}

set_option maxRecDepth 100000 in
/-- **The ring switch's capacity and challenges, natively**: at `verify_keccak`'s returns from `s'` with a full
queue and the stream's word `n` at its cursor, `.n 3033 … 3037` hold `ringCap (s'.nonceState n)`, `.n 3026` its
`ρ`, `.n 3027` its `λ`. -/
theorem VsCtx.ring_nat {s' : Fs} {bm nx : ℕ} {kw n : E} (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n]) :
    [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)] = ringCap (s'.nonceState n) ∧
      x.σ0 (.n 3026) = ringRho (s'.nonceState n) ∧ x.σ0 (.n 3027) = ringLam (s'.nonceState n) ∧
      mcW x.σ0 = (ringChs (s'.nonceState n)).take 16 := by
  have ha : x.args.length = 6 := rfl
  have h0 := x.ring_cells hret rvk hpend hrd
  show [vsVal x.rd0 x.w x.args (.n 3033), vsVal x.rd0 x.w x.args (.n 3034), vsVal x.rd0 x.w x.args (.n 3035),
      vsVal x.rd0 x.w x.args (.n 3036), vsVal x.rd0 x.w x.args (.n 3037)] = _ ∧
    vsVal x.rd0 x.w x.args (.n 3026) = _ ∧ vsVal x.rd0 x.w x.args (.n 3027) = _ ∧
      mcW (vsVal x.rd0 x.w x.args) = _
  set S := s'.nonceState n with hS
  set σ := vsVal x.rd0 x.w x.args with hσ
  have g : ∀ a ∈ vsRingRestA, Good x.rd0 vsSL x.w σ a := fun a h => by
    have := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 2552 18
    rw [vsRingRestA_eq, atomsOf_map] at this
    exact this a h
  have g0 : ∀ a ∈ vsW0, Good x.rd0 (storesOf 6 vsAf) x.w σ a := fun a h => vsW0_good ha h
  have z25 : σ (.n 25) = 0 := (g0 (.const (.n 25) (word 0 0)) (memIdx (l := vsW0) 19 rfl)).trans word_zero
  have z26 : σ (.n 26) = 0 := (g0 (.const (.n 26) (word 0 0)) (memIdx (l := vsW0) 20 rfl)).trans word_zero
  have z27 : σ (.n 27) = 0 := (g0 (.const (.n 27) (word 0 0)) (memIdx (l := vsW0) 21 rfl)).trans word_zero
  have z28 : σ (.n 28) = 0 := (g0 (.const (.n 28) (word 0 0)) (memIdx (l := vsW0) 22 rfl)).trans word_zero
  have k1 : (Atom.keccak [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2938, .n 2939, .n 2940, .n 2941,
      .n 2942] [.n 3004, .n 3005, .n 3006, .n 3007, .n 3008, .n 3009, .n 3010, .n 3011, .n 3012, .n 3013, .n 3014,
      .n 3015, .n 3016] false false).Holds x.rd0 σ :=
    holds_of_good' (g _ (memIdx (l := vsRingRestA) 7 rfl)) rfl
  have k2 : (Atom.keccak [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 3012, .n 3013, .n 3014, .n 3015,
      .n 3016] [.n 3025, .n 3026, .n 3027, .n 3028, .n 3029, .n 3030, .n 3031, .n 3032, .n 3033, .n 3034, .n 3035,
      .n 3036, .n 3037] false false).Holds x.rd0 σ :=
    holds_of_good' (g _ (memIdx (l := vsRingRestA) 16 rfl)) rfl
  clear_value σ
  have o08 : σ (.n 2938) = cellsOfState S false 8 := outs_eq h0 8 (by simp)
  have o09 : σ (.n 2939) = cellsOfState S false 9 := outs_eq h0 9 (by simp)
  have o010 : σ (.n 2940) = cellsOfState S false 10 := outs_eq h0 10 (by simp)
  have o011 : σ (.n 2941) = cellsOfState S false 11 := outs_eq h0 11 (by simp)
  have o012 : σ (.n 2942) = cellsOfState S false 12 := outs_eq h0 12 (by simp)
  have hin1 : List.map σ [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2938, .n 2939,
      .n 2940, .n 2941, .n 2942] = List.replicate 8 0 ++ capOf S := by
    simp only [List.map_cons, List.map_nil, z25, z26, z27, z28, o08, o09, o010, o011, o012]
    rfl
  have hK1 := (keccakA_perm k1).2.2
  rw [hin1] at hK1
  have o18 : σ (.n 3012) = cellsOfState (Link.pkPerm (capOf S)) false 8 := outs_eq hK1 8 (by simp)
  have o19 : σ (.n 3013) = cellsOfState (Link.pkPerm (capOf S)) false 9 := outs_eq hK1 9 (by simp)
  have o110 : σ (.n 3014) = cellsOfState (Link.pkPerm (capOf S)) false 10 := outs_eq hK1 10 (by simp)
  have o111 : σ (.n 3015) = cellsOfState (Link.pkPerm (capOf S)) false 11 := outs_eq hK1 11 (by simp)
  have o112 : σ (.n 3016) = cellsOfState (Link.pkPerm (capOf S)) false 12 := outs_eq hK1 12 (by simp)
  have hin2 : List.map σ [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 3012, .n 3013,
      .n 3014, .n 3015, .n 3016] = List.replicate 8 0 ++ capOf (Link.pkPerm (capOf S)) := by
    simp only [List.map_cons, List.map_nil, z25, z26, z27, z28, o18, o19, o110, o111, o112]
    rfl
  have hK2 := (keccakA_perm k2).2.2
  rw [hin2] at hK2
  set P1 := Link.pkPerm (capOf S) with hP1
  set P2 := Link.pkPerm (capOf P1) with hP2
  have o20 : σ (.n 3025) = cellsOfState P2 false 0 := outs_eq hK2 0 (by simp)
  have o21 : σ (.n 3026) = cellsOfState P2 false 1 := outs_eq hK2 1 (by simp)
  have o22 : σ (.n 3027) = cellsOfState P2 false 2 := outs_eq hK2 2 (by simp)
  have o28 : σ (.n 3033) = cellsOfState P2 false 8 := outs_eq hK2 8 (by simp)
  have o29 : σ (.n 3034) = cellsOfState P2 false 9 := outs_eq hK2 9 (by simp)
  have o210 : σ (.n 3035) = cellsOfState P2 false 10 := outs_eq hK2 10 (by simp)
  have o211 : σ (.n 3036) = cellsOfState P2 false 11 := outs_eq hK2 11 (by simp)
  have o212 : σ (.n 3037) = cellsOfState P2 false 12 := outs_eq hK2 12 (by simp)
  -- the map's challenges
  have cp : ∀ (d s : ℕ) (i : ℕ), vsRingRestA[i]? = some (.copy (.n d) (.n s)) → σ (.n d) = σ (.n s) :=
    fun d s i h => g (.copy (.n d) (.n s)) (memIdx i h)
  have q0 : σ (.n 2997) = challengeOf S := by
    rw [cp 2997 2930 0 rfl, LeanVM.Guest.Value.Keccak.challengeOf_cells]; exact outs_eq h0 0 (by simp)
  have q2 : σ (.n 2998) = packedChallengeOf S 2 := by
    rw [cp 2998 2932 1 rfl, Link.packedChallengeOf_cell S (by norm_num)]; exact outs_eq h0 2 (by simp)
  have q3 : σ (.n 2999) = packedChallengeOf S 3 := by
    rw [cp 2999 2933 2 rfl, Link.packedChallengeOf_cell S (by norm_num)]; exact outs_eq h0 3 (by simp)
  have q4 : σ (.n 3000) = packedChallengeOf S 4 := by
    rw [cp 3000 2934 3 rfl, Link.packedChallengeOf_cell S (by norm_num)]; exact outs_eq h0 4 (by simp)
  have q5 : σ (.n 3001) = packedChallengeOf S 5 := by
    rw [cp 3001 2935 4 rfl, Link.packedChallengeOf_cell S (by norm_num)]; exact outs_eq h0 5 (by simp)
  have q6 : σ (.n 3002) = packedChallengeOf S 6 := by
    rw [cp 3002 2936 5 rfl, Link.packedChallengeOf_cell S (by norm_num)]; exact outs_eq h0 6 (by simp)
  have q7 : σ (.n 3003) = packedChallengeOf S 7 := by
    rw [cp 3003 2937 6 rfl, Link.packedChallengeOf_cell S (by norm_num)]; exact outs_eq h0 7 (by simp)
  have p0 : σ (.n 3017) = Link.cellAt P1 0 := by rw [cp 3017 3004 8 rfl]; exact outs_eq hK1 0 (by simp)
  have p1 : σ (.n 3018) = Link.cellAt P1 1 := by rw [cp 3018 3005 9 rfl]; exact outs_eq hK1 1 (by simp)
  have p2 : σ (.n 3019) = Link.cellAt P1 2 := by rw [cp 3019 3006 10 rfl]; exact outs_eq hK1 2 (by simp)
  have p3 : σ (.n 3020) = Link.cellAt P1 3 := by rw [cp 3020 3007 11 rfl]; exact outs_eq hK1 3 (by simp)
  have p4 : σ (.n 3021) = Link.cellAt P1 4 := by rw [cp 3021 3008 12 rfl]; exact outs_eq hK1 4 (by simp)
  have p5 : σ (.n 3022) = Link.cellAt P1 5 := by rw [cp 3022 3009 13 rfl]; exact outs_eq hK1 5 (by simp)
  have p6 : σ (.n 3023) = Link.cellAt P1 6 := by rw [cp 3023 3010 14 rfl]; exact outs_eq hK1 6 (by simp)
  have p7 : σ (.n 3024) = Link.cellAt P1 7 := by rw [cp 3024 3011 15 rfl]; exact outs_eq hK1 7 (by simp)
  have p20 : σ (.n 3038) = Link.cellAt P2 0 := by rw [cp 3038 3025 17 rfl, o20]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o28, o29, o210, o211, o212]
    show _ = capOf P2
    rfl
  · rw [ringRho_eq, o21]
    rfl
  · rw [ringLam_eq, o22]
    rfl
  · show (vsMcV.map fun i => σ (.n i)) = _
    simp only [vsMcV, List.map_cons, List.map_nil]
    rw [q0, q2, q3, q4, q5, q6, q7, p0, p1, p2, p3, p4, p5, p6, p7, p20]
    unfold ringChs
    rw [VerifySub.grindPacked_list]
    rfl

/-- **`.n 2921`, natively**: `verify_keccak`'s word. -/
theorem VsCtx.kw_nat {s' : Fs} {bm nx : ℕ} {kw : E} (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0) :
    x.σ0 (.n 2921) = kw := by
  have ha : x.args.length = 6 := rfl
  have r35 := vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC35_eq
  exact (r35 (.n 2921) (by simp)).trans (vsW_retC ha hret (i := 2915 + 6) (by decide) (rvk 6 (by norm_num)))

end

/-! ## (c) The target -/

/-- **The guest's Horner sum is the stacked target** once the claims' values are, in order, the merged ring
claim's, `m1`, the first `55` sent words, the public input's two, the Keccak word, the out-of-domain value. -/
theorem vsOpenTarget_eq {rt lam m1 p0 p1 kw ood : E} {sent : List E} {claims : List StackClaim}
    (h : claims.map (·.2) = rt :: m1 :: (sent.take 55 ++ [p0, p1, kw]) ++ [ood]) :
    vsOpenTarget rt lam m1 p0 p1 kw ood sent = dot (powers lam claims.length) (claims.map (·.2)) := by
  rw [show claims.length = (claims.map (·.2)).length from (List.length_map _).symm, dot_powers_hornerL, h]
  simp only [vsOpenTarget, hornerL, List.cons_append, List.nil_append, List.append_assoc]
  ring

/-- The stream is at least `13` words long. -/
theorem NatOpen.Ok.len13 {N : NatOpen} {seed : Digest} {c : Child} (hN : N.Ok seed c) :
    13 ≤ c.proof.stream.length := by
  have h := congrArg List.length hN.hw
  rw [List.length_drop, List.length_append, hN.hrest] at h
  simp only [List.length_append, List.length_cons] at h
  omega

/-- The announced layout is built. -/
theorem NatOpen.Ok.build {N : NatOpen} {seed : Digest} {c : Child} (hN : N.Ok seed c) :
    ∃ lm rows, buildLayout guestBytecode lm rows = some N.layout := by
  have hs := announced_eq_run (fun _ ↦ default) (fun _ ↦ default) guestBytecode
    (s := ⟨⟨default, [], none⟩, c.proof.stream, [], []⟩) rfl
  have hsz : sizesOf guestBytecode (c.proof.stream.take (2 + nTables)) = some (N.layout, N.r) := by
    have e := hs.symm.trans hN.hann
    rw [run_readSizes _ _ guestBytecode rfl] at e
    split at e
    · exact e
    · cases e
  obtain ⟨-, -, -, -, lm, rows, hb⟩ := sizesOf_facts hsz
  exact ⟨lm, rows, hb⟩

/-- **The native claims' values** (`phOpen_of_ood`'s `hvals`, forwards): the merged ring claim's target, `m1`, the
message's first `55` words (the link's column values with a placement), the public input's two, the Keccak word,
the out-of-domain value. -/
theorem NatOpen.Ok.vals {N : NatOpen} {seed : Digest} {c : Child} (hN : N.Ok seed c) {op : List E} {kw : E}
    (hout : N.outs = [⟨qkeccak, op, kw⟩]) :
    (N.claims seed c).map (·.2) =
      (ringMerge [keccakRingClaim N.qp N.kp N.ks, N.link.ring] (ringF N.S) (ringG N.S) (ringRho N.S)).2 ::
        N.L.m1 :: (N.L.msg.take 55 ++ [N.v0, N.v1, kw]) ++ [c.proof.stream.getD 11 0] := by
  obtain ⟨lm, rows, hb⟩ := hN.build
  have htab := buildLayout_tables hb
  have hm := hN.hL.lenM
  have hlk := hN.hL.link
  set F := natF3 seed c N.layout.stackLog
  obtain ⟨Vals, hVals⟩ : ∃ W, W = N.link.columns.flatMap fun c ↦ c.2.map (·.2) := ⟨_, rfl⟩
  have hcols : N.link.columns.map (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦
        ((N.L.chi N.layout F).take (N.layout.tableLogHeights.getD t 0), nonPointerColumns table)) := by
    rw [hlk]; exact VerifySub.end_columns_shape htab _ _ _ _ _ _ _ _ _ hm
  have hV80 : Vals = (List.range 80).map (N.L.msg.getD · 0) := by
    rw [hVals, hlk]; exact VerifySub.end_columns_values htab _ _ _ _ _ _ _ _ _ hm
  have hcl6 : N.link.columns.length = 6 := by
    have := congrArg List.length hcols
    simp only [List.length_map, List.length_zipIdx] at this
    rw [this]; rfl
  have hLCc := linkColumnClaims_colPts N.link
    (fun t ↦ (N.L.chi N.layout F).take (N.layout.tableLogHeights.getD t 0)) hcols
  have hLCcol : (linkColumnClaims N.link).map (·.column) = (sentCols.zip sentKinds).map (·.1.2) := by
    have h1 := congrArg (List.map Prod.fst) hLCc
    simp only [List.map_map] at h1
    rw [show ((sentCols.zip sentKinds).map fun z ↦ z.1.2) = ((sentCols.zip sentKinds).map Prod.fst).map Prod.snd by
        simp [List.map_map],
      List.map_fst_zip (by rw [sent_ok.1]; rfl)]
    exact h1
  have hLClen : (linkColumnClaims N.link).length = 80 := by
    have := congrArg List.length hLCc
    simp only [List.length_map] at this
    rw [this, sent_ok.1]
  have hLCv : ((linkColumnClaims N.link).filterMap (·.onStack N.layout)).map (·.2) = Vals.take 55 := by
    rw [VerifySub.onStack_vals hb _ _ sent_ok.2 hLCcol,
      VerifySub.filter_zip_take (fun c : ColumnClaim ↦ c.value) (fun z : (ℕ × ℕ) × ℕ ↦ z.2 != 1000) _ _ 55
        (by rw [hLClen, List.length_zip, sent_ok.1]; rfl) ?_,
      VerifySub.lcc_values N.link (by rw [hcl6]; decide), ← hVals]
    intro i hi
    rw [List.getElem_zip]
    have hk : ∀ i (h : i < sentKinds.length), ((sentKinds[i] != 1000) = true ↔ i < 55) := by
      decide +kernel
    exact hk i _
  have hV55 : Vals.take 55 = N.L.msg.take 55 := by
    rw [hV80]
    apply List.ext_getElem (by simp [hm])
    intro i h1 h2
    simp only [List.length_take, List.length_map, List.length_range] at h1
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega)]
  obtain ⟨p0, hp0⟩ := VerifySub.placement_of_buildLayout hb (c := memory0) (by decide)
  obtain ⟨p1, hp1⟩ := VerifySub.placement_of_buildLayout hb (c := memory1) (by decide)
  have hmt := hN.hmt
  have hmt2 : N.mt.2 = N.L.m1 := by
    simp only [memoryTermPure, hp0, hp1, Option.some.injEq] at hmt
    rw [← hmt, hlk]
    rfl
  have hpub2 : ((publicClaimsPure N.layout (N.rm seed c) N.v0 N.v1).filterMap (·.onStack N.layout)).map (·.2) =
      [N.v0, N.v1] := by
    simp only [publicClaimsPure, List.filterMap_cons, List.filterMap_nil, ColumnClaim.onStack, hp0, hp1,
      Option.map_some, List.map_cons, List.map_nil]
  have hout2 : (N.outs.filterMap (·.onStack N.layout)).map (·.2) = [kw] := by
    simp only [hout, List.filterMap_cons, List.filterMap_nil, ColumnClaim.onStack, hN.hqp, Option.map_some,
      List.map_cons, List.map_nil]
  simp only [NatOpen.claims, NatOpen.ood, List.map_cons, List.map_append, List.map_nil, hmt2]
  rw [List.filterMap_append, List.filterMap_append, List.map_append, List.map_append, hLCv, hpub2, hout2, hV55]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-! ### The guest's values of the target's terms -/

section
variable {x : VsCtx} {L : LinkNat}
open LeanVM.Guest.B1.Link

/-- **`.n 779`, natively**: `m1`, the stream's word past the index side's rounds (vsnat2's `g2_of`, its load). -/
theorem VsCtx.m1_nat {rest : List E} (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hbits : L.bits x.lay ≠ 0) (hwd : L.chunks.width ≠ 0) (hlI : L.wsI.length = L.chunks.width * natRoundLen 1 0)
    (hret : CausalRule x.ret) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hrd0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (x.bw.getD 18 []))
    (r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0) :
    x.σ0 (.n 779) = L.m1 := by
  have ha : x.args.length = 6 := rfl
  show vsVal x.rd0 x.w x.args (.n 779) = _
  have hg := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 259 11
  have hm : ∀ a ∈ ([.copy (.n 774) (.n 767), .copy (.n 775) (.n 768), .copy (.n 776) (.n 769),
      .copy (.n 777) (.n 770), .copy (.n 778) (.n 771), .load (.n 779) (.n 772) 0, .copy (.n 780) (.n 779),
      .const (.n 781) (word 0 1),
      .keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775, .n 776, .n 777, .n 778]
        [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792, .n 793, .n 794]
        false false] : List Atom), Good x.rd0 vsSL x.w (vsVal x.rd0 x.w x.args) a := fun a h =>
    hg a (by simpa using List.all_eq_true.mp vsC13_kAtoms a h)
  set σ := vsVal x.rd0 x.w x.args with hσσ
  have hne : x.natLI L ≠ [] := natChain_ne hwd _ _
  have hcap : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap.length = 5 := natChain_last_cap hwd _ _ _
  have hr : ∀ j < 7, σ (.n (767 + j)) = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0 := fun j hj => by
    have e1 : σ (.n (767 + j)) = x.w (767 + j) :=
      vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC12_eq (.n (767 + j)) (by interval_cases j <;> simp)
    rw [e1]
    exact vsW_retC ha hret (by interval_cases j <;> decide) (r767 j hj)
  have hcur : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cur = ptrAt (x.natB772 L) := by
    rw [chainLast_ne hne _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩, VsCtx.natLI, LinkNat.chainI, natChain_cur, ← hlI,
      ptrAt_add]
    rfl
  have e772 : σ (.n 772) = ptrAt (x.natB772 L) := by
    rw [show (772 : ℕ) = 767 + 5 from rfl, hr 5 (by norm_num), cells_getD_5 hcap, hcur]
  obtain ⟨tl, htl⟩ := padStream_drop13 hbits hw
  have hT0 : ReadsAt x.rd0 (ptrAt x.sI) (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl)))) := by
    have := VsC.readsAt_drop (m := 13) hrd0
    rwa [hb18, htl] at this
  have hm1 : ReadsAt x.rd0 (ptrAt (x.natB772 L)) [L.m1] := by
    have := readsAt_slice hT0 L.wsI.length 1
    rwa [List.drop_left' rfl, List.take_succ_cons, List.take_zero] at this
  exact good_load_get? (by intro h; have fr := vsC13_fresh; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr (by decide))
    (hm (.load (.n 779) (.n 772) 0) (by simp)) e772 hm1 rfl

/-- **The message at the packed cursor**: the native message, word for word. -/
theorem VsCtx.msg_nat {rest : List E} (hb : L.bits x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144) :
    x.sw (x.natBm L) 0 144 = L.msg := by
  unfold VsCtx.sw
  rw [Nat.add_zero]
  exact (x.sw_nat hb hw hb18 hm).1

/-- **`.n 1287`, natively**: `packed_message`'s first return, the public input's challenge. -/
theorem VsCtx.rm_nat {rest : List E} (hret : CausalRule x.ret) (hb : L.bits x.lay ≠ 0)
    (hq : linkQVars x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0) :
    x.σ0 (.n 1287) = (L.F4 x.lay x.nF).squeeze.1 := by
  have ha : x.args.length = 6 := rfl
  have r19 : ∀ v ∈ [V.n 1287, .n 1288, .n 1289, .n 1290, .n 1291, .n 1292], x.σ0 v = x.w v.idx :=
    vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC19_eq
  have e0 : x.w 1287 = _ := vsW_retC ha hret (i := 1287 + 0) (by decide) (r1287 0 (by norm_num))
  have hxm : ((x.bw.getD 18 []).drop (x.natBm L - x.base 18)).take 144 = L.msg := (x.sw_nat hb hw hb18 hm).1
  have hpm : x.natPm L = (L.F4 x.lay x.nF).squeeze.1 :: (L.F4 x.lay x.nF).squeeze.2.cap := by
    unfold VsCtx.natPm pmRets LinkNat.F4
    rw [hxm, x.natLC_cap hq]
  rw [r19 (.n 1287) (by simp), e0, hpm, List.getD_cons_zero]

/-- **`.n 3810`, natively**: `ring_switch_target`'s honest return on the merged slices (`bw 15`'s first `64`, the
Keccak slices, plus `ρ` times the message's words from `80`) and the map's challenges is the merged ring claim's
target (`ringMerge_two_snd`). -/
theorem VsCtx.h3810_nat {N : NatOpen} (hN : N.Ok x.seed x.c) {bm : ℕ} (hret : CausalRule x.ret)
    (r3810 : ∀ σ, x.ret 3810 σ = ringTarget (rsW (x.bw.getD 15 []) (x.sw bm 0 144) (x.σ0 (.n 3026)))
      ((mcW x.σ0).take 8) ((mcW x.σ0).drop 8))
    (h15 : (x.bw.getD 15 []).take 64 = N.ks) (hks : N.ks.length = kBits) (hmsg : x.sw bm 0 144 = N.L.msg)
    (hrho : x.σ0 (.n 3026) = ringRho N.S) (hmc : mcW x.σ0 = (ringChs N.S).take 16) :
    x.σ0 (.n 3810) =
      (ringMerge [keccakRingClaim N.qp N.kp N.ks, N.link.ring] (ringF N.S) (ringG N.S) (ringRho N.S)).2 := by
  have ha : x.args.length = 6 := rfl
  have r37 := vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC37_eq
  have e1 : x.σ0 (.n 3810) = x.w 3810 := r37 (.n 3810) (by simp)
  have e2 : x.w 3810 = ringTarget (rsW (x.bw.getD 15 []) (x.sw bm 0 144) (x.σ0 (.n 3026)))
      ((mcW x.σ0).take 8) ((mcW x.σ0).drop 8) := vsW_retC ha hret (i := 3810) (by decide) r3810
  obtain ⟨lm, rows, hb⟩ := hN.build
  have htab := buildLayout_tables hb
  have hm := hN.hL.lenM
  have hsl : N.link.ring.slices = N.L.msg.drop 80 := by
    rw [hN.hL.link]
    show N.L.msg.drop (LeanVM.Guest.B1.Link.Arith.tailNValues N.layout) = _
    rw [VerifySub.tailNValues_tables htab]
  have hsll : N.link.ring.slices.length = kBits := by
    rw [hsl, List.length_drop, hm]; rfl
  rw [e1, e2, hrho, hmc, hmsg, VerifySub.ringMerge_two_snd _ _ _ _ _ _ _ hks hsll]
  have hA : rsW (x.bw.getD 15 []) N.L.msg (ringRho N.S) =
      (List.range kBits).map fun i => N.ks.getD i 0 + ringRho N.S * N.link.ring.slices.getD i 0 := by
    unfold rsW
    rw [show kBits = 64 from rfl]
    refine List.map_congr_left (fun i hi => ?_)
    have hi' : i < 64 := List.mem_range.mp hi
    rw [← h15, hsl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi']
  have hF : ((ringChs N.S).take 16).take 8 = ringF N.S := by
    rw [List.take_take]; rfl
  have hG : ((ringChs N.S).take 16).drop 8 = ringG N.S := by
    rw [List.drop_take]; rfl
  rw [hA, hF, hG]

end

/-! ### The public input's two values -/

/-- Statements `2906 ..< 2922` (`vsC`'s `2478 ..< 2494`): the public input's limbs and their lines. -/
def vsPubA : List Atom :=
  [.hint (.limbs (.n 0) [.n 2895]), .add (.n 2896) (.n 0) (.n 2895), .const (.n 2897) (word 2 1),
    .mul (.n 2898) (.n 2896) (.n 2897), .assertInK (.n 2895) (.n 2898),
    .hint (.limbs (.n 1) [.n 2899]), .add (.n 2900) (.n 1) (.n 2899), .const (.n 2901) (word 2 1),
    .mul (.n 2902) (.n 2900) (.n 2901), .assertInK (.n 2899) (.n 2902),
    .add (.n 2903) (.n 2895) (.n 2899), .mul (.n 2904) (.n 1287) (.n 2903), .add (.n 2905) (.n 2895) (.n 2904),
    .add (.n 2906) (.n 2898) (.n 2902), .mul (.n 2907) (.n 1287) (.n 2906), .add (.n 2908) (.n 2898) (.n 2907)]

set_option maxRecDepth 200000 in
theorem vsPubA_eq : (vsC.drop 2478).take 16 = vsPubA.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem pub_line (x y c : E) : multilinearEval [x, y] [c] = x + c * (x + y) := by
  simp [multilinearEval, foldPairs]
  ring

section
variable {x : VsCtx}

/-- **`.n 2905`, `.n 2908`, natively**: the statement digest's limbs on their lines at `.n 1287`. -/
theorem VsCtx.pub_nat :
    x.σ0 (.n 2905) = pubV (statementDigest x.seed x.c.statement) (x.σ0 (.n 1287)) 0 ∧
      x.σ0 (.n 2908) = pubV (statementDigest x.seed x.c.statement) (x.σ0 (.n 1287)) 1 := by
  have ha : x.args.length = 6 := rfl
  show vsVal x.rd0 x.w x.args (.n 2905) = pubV _ (vsVal x.rd0 x.w x.args (.n 1287)) 0 ∧
    vsVal x.rd0 x.w x.args (.n 2908) = pubV _ (vsVal x.rd0 x.w x.args (.n 1287)) 1
  have p0 : vsVal x.rd0 x.w x.args (.n 0) = (digestHalves (statementDigest x.seed x.c.statement)).1 := by
    rw [vsVal_param ha (i := 0) (by norm_num)]; rfl
  have p1 : vsVal x.rd0 x.w x.args (.n 1) = (digestHalves (statementDigest x.seed x.c.statement)).2 := by
    rw [vsVal_param ha (i := 1) (by norm_num)]; rfl
  set σ := vsVal x.rd0 x.w x.args with hσ
  have g : ∀ a ∈ vsPubA, Good x.rd0 vsSL x.w σ a := fun a h => by
    have := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 2478 16
    rw [vsPubA_eq, atomsOf_map] at this
    exact this a h
  have l0 : σ (.n 2895) = limbAt (σ (.n 0)) 0 := g _ (memIdx (l := vsPubA) 0 rfl) 0 (by simp)
  have a1 : σ (.n 2896) = σ (.n 0) + σ (.n 2895) := g _ (memIdx (l := vsPubA) 1 rfl)
  have c2 : σ (.n 2897) = word 2 1 := g _ (memIdx (l := vsPubA) 2 rfl)
  have m3 : σ (.n 2898) = σ (.n 2896) * σ (.n 2897) := by
    have := g _ (memIdx (l := vsPubA) 3 rfl)
    simp only [Good, show (V.n 2896).idx < (V.n 2898).idx ∧ (V.n 2897).idx < (V.n 2898).idx from by decide]
      at this
    exact this
  have l5 : σ (.n 2899) = limbAt (σ (.n 1)) 0 := g _ (memIdx (l := vsPubA) 5 rfl) 0 (by simp)
  have a6 : σ (.n 2900) = σ (.n 1) + σ (.n 2899) := g _ (memIdx (l := vsPubA) 6 rfl)
  have c7 : σ (.n 2901) = word 2 1 := g _ (memIdx (l := vsPubA) 7 rfl)
  have m8 : σ (.n 2902) = σ (.n 2900) * σ (.n 2901) := by
    have := g _ (memIdx (l := vsPubA) 8 rfl)
    simp only [Good, show (V.n 2900).idx < (V.n 2902).idx ∧ (V.n 2901).idx < (V.n 2902).idx from by decide]
      at this
    exact this
  have a10 : σ (.n 2903) = σ (.n 2895) + σ (.n 2899) := g _ (memIdx (l := vsPubA) 10 rfl)
  have m11 : σ (.n 2904) = σ (.n 1287) * σ (.n 2903) := by
    have := g _ (memIdx (l := vsPubA) 11 rfl)
    simp only [Good, show (V.n 1287).idx < (V.n 2904).idx ∧ (V.n 2903).idx < (V.n 2904).idx from by decide]
      at this
    exact this
  have a12 : σ (.n 2905) = σ (.n 2895) + σ (.n 2904) := g _ (memIdx (l := vsPubA) 12 rfl)
  have a13 : σ (.n 2906) = σ (.n 2898) + σ (.n 2902) := g _ (memIdx (l := vsPubA) 13 rfl)
  have m14 : σ (.n 2907) = σ (.n 1287) * σ (.n 2906) := by
    have := g _ (memIdx (l := vsPubA) 14 rfl)
    simp only [Good, show (V.n 1287).idx < (V.n 2907).idx ∧ (V.n 2906).idx < (V.n 2907).idx from by decide]
      at this
    exact this
  have a15 : σ (.n 2908) = σ (.n 2898) + σ (.n 2907) := g _ (memIdx (l := vsPubA) 15 rfl)
  clear_value σ
  have lo0 : σ (.n 2895) = ofK ((σ (.n 0)).limb 0) := l0
  have lo1 : σ (.n 2899) = ofK ((σ (.n 1)).limb 0) := l5
  have hi0 : σ (.n 2898) = ofK ((σ (.n 0)).limb 1) := by
    rw [m3, c2, a1, lo0, word_y_inv, LeanVM.Guest.Value.split_hi]
  have hi1 : σ (.n 2902) = ofK ((σ (.n 1)).limb 1) := by
    rw [m8, c7, a6, lo1, word_y_inv, LeanVM.Guest.Value.split_hi]
  refine ⟨?_, ?_⟩
  · rw [a12, m11, a10, lo0, lo1, p0, p1]
    exact (pub_line _ _ _).symm
  · rw [a15, m14, a13, hi0, hi1, p0, p1]
    exact (pub_line _ _ _).symm

end

/-! ## (d) The root's halves -/

section
variable {x : VsCtx}

/-- **`.n 134`, `.n 137`, natively**: the stream's words `8`, `9`, loaded from the stream's buffer. -/
theorem VsCtx.stream89_nat (hx : x.HonB) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hl : 10 ≤ x.c.proof.stream.length) :
    x.σ0 (.n 134) = x.c.proof.stream.getD 8 0 ∧ x.σ0 (.n 137) = x.c.proof.stream.getD 9 0 := by
  have ha : x.args.length = 6 := rfl
  have h0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (padStream x.c.proof.stream) := by
    rw [← hb18]; exact x.reads18B hx
  have hw55 : x.w 55 = ptrAt (x.base 18) := vsW_buf (rd1 := x.rd1) ha hx.hret (j := 18) (by norm_num) rfl
  have g6 := vsW6_good (rd0 := x.rd0) (w := x.w) ha
  have p55 : vsVal x.rd0 x.w x.args (.n 55) = ptrAt (x.base 18) := by rw [vsVal_55 ha, hw55]
  have hpl : x.c.proof.stream.length ≤ (padStream x.c.proof.stream).length := by simp [padStream]
  refine ⟨?_, ?_⟩
  · show vsVal x.rd0 x.w x.args (.n 134) = _
    rw [good_loadAt (vsW6_freshAt (d := 134) (pv := 55) (off := 8) (by simp [vsW6ld]) (by decide))
      (g6 _ (mem_of_getElem?' (l := vsW6) 25 rfl)) p55 (by omega) h0, getElem_getD, padStream_getDF (by omega)]
  · show vsVal x.rd0 x.w x.args (.n 137) = _
    rw [good_loadAt (vsW6_freshAt (d := 137) (pv := 55) (off := 9) (by simp [vsW6ld]) (by decide))
      (g6 _ (mem_of_getElem?' (l := vsW6) 28 rfl)) p55 (by omega) h0, getElem_getD, padStream_getDF (by omega)]

/-- **The out-of-domain value at `.n 23`**: the stream's word `11`. -/
theorem VsCtx.ood_nat (hB : x.BwFs) (hl : 12 ≤ x.c.proof.stream.length) :
    (x.bw.getD 17 []).getD 0 0 = x.c.proof.stream.getD 11 0 := by
  rw [hB.b17]
  exact padStream_getDF (by omega)

end

/-! ## (e) The call's region and (f) its post -/

section
variable {x : VsCtx}

/-- **`open_stacked`'s call, natively**: at `ic = bm + 144 + nx + 1` past the Keccak reduction's words and the
ring's nonce, reading `N.ws` in the buffers (the stream's buffer holds them) and the window tables in the
caller's region, from `open_stacked`'s completeness at `natOpen`'s run. -/
theorem VsCtx.openCall_nat (hO : ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs x.al B2C.cert 17 m)
    {N : NatOpen} (hN : N.Ok x.seed x.c) {bm nx : ℕ} (hbm : x.base 18 ≤ bm)
    (hin : bm + 144 + nx + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) (kc : ℕ) :
    ∃ bp bp1 e : ℕ, CallAtA B2C.fs x.al B2C.cert 17 (openName N.layout.stackLog)
      (rateSel N.r :: ringCap N.S ++ [N.target x.seed x.c, x.c.proof.stream.getD 8 0, x.c.proof.stream.getD 9 0,
        ptrAt (bm + 144 + nx + 1), ptrAt (x.qt + 178)])
      (osRets N.wE bp bp1 (bm + 144 + nx + 1 + N.ws.length)) (fun i => x.R i ∨ x.OwnB i)
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
        ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1))
      (fun rd => ReadsAt rd (ptrAt (bm + 144 + nx + 1)) N.ws ∧ WinTabs rd (ptrAt (x.qt + 178)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (openName N.layout.stackLog)) (allocBase (x.al (openName N.layout.stackLog)) kc)
      (allocBase (x.al (openName N.layout.stackLog)) kc + B2C.fs (openName N.layout.stackLog)) e := by
  have B18 := (bases_of (x := x)).b18
  have hsum := vsAllocSz_sum x.p
  have hxs : ∀ i < N.ws.length, x.R (bm + 144 + nx + 1 + i) ∨ x.OwnB (bm + 144 + nx + 1 + i) :=
    fun i hi => Or.inr (show x.cur ≤ _ ∧ _ < x.cur + (vsAllocSz x.p).sum from ⟨by omega, by omega⟩)
  have hit : ∀ n < 2 ^ winTabBits, x.R (x.qt + 178 + n) ∨ x.OwnB (x.qt + 178 + n) := fun n hn => by
    have h2 : 2 ^ winTabBits = 2048 := rfl
    exact Or.inl (show (x.qt ≤ x.qt + 178 + n ∧ x.qt + 178 + n < x.qt + expTabLen) ∨ _ from
      Or.inl ⟨by omega, by rw [expTabLen_eq]; omega⟩)
  have hh := digestScalars_digestOfScalars (x.c.proof.stream.getD 8 0, x.c.proof.stream.getD 9 0)
  have e8 : x.c.proof.stream.getD 8 0 = (digestHalves (natRoot x.c)).1 := by rw [natRoot, hh]
  have e9 : x.c.proof.stream.getD 9 0 = (digestHalves (natRoot x.c)).2 := by rw [natRoot, hh]
  rw [e8, e9]
  have hsp : ∃ sp : Sponge, (⟨ringCap N.S, []⟩ : Fs).Carries sp :=
    carries_capOf (Link.pkPerm (capOf (Link.pkPerm (capOf N.S))))
  exact openCall_of hO hN.shape.stack_ge hN.shape.stack_le hN.shape.rate_ge hN.shape.rate_le (ringCap_length _) hsp
    hN.hos hN.hq hxs hit kc

/-- **`D3.Ok.hQo` at `open_stacked`'s native post**: its pops are the child's Merkle hints. -/
theorem VsCtx.hQo_nat (x : VsCtx) (Oo : Reader → Prop) :
    ∀ rd, LowDef 17 rd → x.Pre rd → Oo rd → ∀ t,
      SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd) →
      PopsPost (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) rd t :=
  fun _ _ _ _ _ h => h

/-- **`D3.Ok.hos` at the honest context**: `open_stacked`'s native call (`openCall_nat`, at `D`'s ends, buffers and
cursor), with the guest's values the native ones: the rate (`h96_nat`), the ring's capacity and `λ`
(`ring_nat`, from `verify_keccak`'s returns `rvk` at `N.s'` and the nonce `N.n` read at the cursor), the target
(`vsOpenTarget_eq`, `NatOpen.Ok.vals`, with the merged ring claim's target `h3810`, `m1` at `.n 779`, the public
input's values from `.n 1287`'s challenge `h1287` (`pub_nat`) and the message's first `55` words `hmsg`), the root's halves (`stream89_nat`). -/
theorem VsCtx.hos_honest (x : VsCtx) (D : D3) {N : NatOpen} (hN : N.Ok x.seed x.c) {op : List E}
    (hout : N.outs = [⟨qkeccak, op, D.kw⟩]) (hx : x.HonB) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hR : x.Ret1F) (hB : x.BwFs) (hsl : D.sl = N.layout.stackLog)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets N.s' (ptrAt (D.bm + 144)) D.nx D.kw).getD j 0)
    (hpend : N.s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (D.bm + 144 + D.nx)) [N.n])
    (h3810 : x.σ0 (.n 3810) =
      (ringMerge [keccakRingClaim N.qp N.kp N.ks, N.link.ring] (ringF N.S) (ringG N.S) (ringRho N.S)).2)
    (h779 : x.σ0 (.n 779) = N.L.m1) (h1287 : x.σ0 (.n 1287) = N.rm x.seed x.c)
    (hmsg : (x.sw D.bm 0 144).take 55 = N.L.msg.take 55)
    (hcall : CallAtA B2C.fs x.al B2C.cert 17 (openName N.layout.stackLog)
      (rateSel N.r :: ringCap N.S ++ [N.target x.seed x.c, x.c.proof.stream.getD 8 0, x.c.proof.stream.getD 9 0,
        ptrAt (D.bm + 144 + D.nx + 1), ptrAt (x.qt + 178)])
      (osRets D.wE D.bp D.bp1 (D.bm + 144 + D.nx + 1 + D.nxo)) D.Ro D.Do D.Oo D.Po D.Qo
      (B2C.fs (openName N.layout.stackLog)) (allocBase (x.al (openName N.layout.stackLog)) (x.ec 15))
      (allocBase (x.al (openName N.layout.stackLog)) (x.ec 15) + B2C.fs (openName N.layout.stackLog)) (x.ec 16)) :
    CallAtA B2C.fs x.al B2C.cert 17 (openName D.sl)
      (x.σ0 (.n 96) :: [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)] ++
        [vsOpenTarget (x.σ0 (.n 3810)) (x.σ0 (.n 3027)) (x.σ0 (.n 779)) (x.σ0 (.n 2905)) (x.σ0 (.n 2908))
          (x.σ0 (.n 2921)) ((x.bw.getD 17 []).getD 0 0) (x.sw D.bm 0 144), x.σ0 (.n 134), x.σ0 (.n 137),
          ptrAt (D.bm + 144 + D.nx + 1), ptrAt (x.qt + 178)])
      (osRets D.wE D.bp D.bp1 (D.bm + 144 + D.nx + 1 + D.nxo)) D.Ro D.Do D.Oo D.Po D.Qo (B2C.fs (openName D.sl))
      (allocBase (x.al (openName D.sl)) (x.ec 15)) (allocBase (x.al (openName D.sl)) (x.ec 15) + B2C.fs (openName D.sl))
      (x.ec 16) := by
  have hl := hN.len13
  have hret := hx.hret
  obtain ⟨hcap', -, hlam', -⟩ := x.ring_nat hret rvk hpend hrd
  have hcap : [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)] = ringCap N.S := hcap'
  have hlam : x.σ0 (.n 3027) = ringLam N.S := hlam'
  obtain ⟨h134, h137⟩ := x.stream89_nat hx hb18 (by omega)
  have h96 := x.h96_nat hret hR hN.hann hN.shape.rate_ge
  obtain ⟨h2905', h2908'⟩ := x.pub_nat
  have h2905 : x.σ0 (.n 2905) = N.v0 := by rw [h2905', h1287, hN.hv0]
  have h2908 : x.σ0 (.n 2908) = N.v1 := by rw [h2908', h1287, hN.hv1]
  have htg : vsOpenTarget (x.σ0 (.n 3810)) (x.σ0 (.n 3027)) (x.σ0 (.n 779)) (x.σ0 (.n 2905)) (x.σ0 (.n 2908))
      (x.σ0 (.n 2921)) ((x.bw.getD 17 []).getD 0 0) (x.sw D.bm 0 144) = N.target x.seed x.c := by
    rw [x.kw_nat hret rvk, x.ood_nat hB (by omega), h3810, hlam, h779, h2905, h2908]
    unfold NatOpen.target
    exact vsOpenTarget_eq (by rw [hN.vals hout, hmsg])
  rw [hsl, h96, hcap, htg, h134, h137]
  exact hcall

end

end
end LeanVM.Guest.B1.VsC
