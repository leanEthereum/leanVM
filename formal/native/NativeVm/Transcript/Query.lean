module

public import NativeVm.Transcript.QueryHead

/-!
# `query`

`query_spec`: from a state that simulates `st`, root `i` in `r9`, the positions `ps` at `r10`
(their count in `r11`) and a rows area at `r12` of `wireMaxLeafWords` words per position, `query`
ends in a state that simulates `queryStep i ps st`'s, the rows' words at `r12` (`QueryRowsAt`), or fails
when it is `none`; either way it writes only the transcript's words (`Foot`) and the rows area, and
`rdi` is kept. The prelude is `queryHead_spec`; each pass of the openings' loop is `openOne_spec`,
and the loop ends normally exactly when every opening checks out (`openPhase_some`,
`openPhase_none_of_not`).
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

variable {env : Env} {st : VerifierProgramState} {s : QState}

theorem opening_le {L p j : Nat} (hp : p < 8) (hj : j < 256) :
    phaseBase L p + 3 + j * openingWords + openingWords ≤ decodedWords L := by
  rw [phaseBase_eq, decodedWords_eq, openingWords_val]
  omega

theorem row_lt {k n w t W : Nat} (hk : k < n) (ht : t < w) (hw : w ≤ W) : k * w + t < n * W :=
  calc k * w + t < (k + 1) * w := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ n * W := Nat.mul_le_mul hk hw

theorem row_disj {k j w t t' : Nat} (hkj : k < j) (ht : t < w) : k * w + t < j * w + t' :=
  calc k * w + t < (k + 1) * w := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ j * w := Nat.mul_le_mul_right _ hkj
    _ ≤ j * w + t' := Nat.le_add_right _ _

theorem climbW_foot {a : UInt64} (h : ClimbW env.ctx a) : Foot env a := by
  rcases h with h | h
  · exact foot_ctx h le_rfl (by lay_omega)
  · exact foot_ctx h (by lay_omega) (by lay_omega)

/-- **`query i positions`**: root `i` in `r9`, the positions `ps` at `r10`, their count in `r11`,
the rows to `r12`, `wireMaxLeafWords` words reserved per position. -/
theorem query_spec {i : Nat} {ps : List Nat} {P R : UInt64} (h : SimState env st s)
    (hi : i < 2 ^ 64) (hps : ∀ q ∈ ps, q < 2 ^ 64) (hlen : ps.length ≤ wireMaxQueries)
    (hr9 : s.reg .r9 = i.toUInt64) (hr10 : s.reg .r10 = P)
    (hr11 : s.reg .r11 = ps.length.toUInt64) (hr12 : s.reg .r12 = R)
    (hP : ∀ j (hj : j < ps.length), s.mem (wd P j) = some ps[j].toUInt64)
    (hfP : Fits P ps.length) (hPc : Disj P ps.length env.ctx ctxEnd)
    (hPw : Disj P ps.length env.work workWords)
    (hfR : Fits R (ps.length * wireMaxLeafWords))
    (hRs : ∀ k < ps.length * wireMaxLeafWords, (s.mem (wd R k)).isSome)
    (hRc : Disj R (ps.length * wireMaxLeafWords) env.ctx ctxEnd)
    (hRd : Disj R (ps.length * wireMaxLeafWords) env.dec (decodedWords env.L))
    (hRw : Disj R (ps.length * wireMaxLeafWords) env.work workWords)
    (hRP : Disj R (ps.length * wireMaxLeafWords) P ps.length) :
    WP query s
      (fun s' ↦ ∃ rows st', queryStep i ps st = some (rows, st') ∧ SimState env st' s' ∧
        QueryRowsAt s'.mem R rows ∧
        Keeps queryClobbers (fun a ↦ Foot env a ∨ InArea R (ps.length * wireMaxLeafWords) a) s s')
      (fun s' ↦ queryStep i ps st = none ∧ s'.reg .rdi = s.reg .rdi ∧
        ∀ a, ¬ Foot env a → ¬ InArea R (ps.length * wireMaxLeafWords) a → s'.mem a = s.mem a) := by
  set n := ps.length with hn_def
  set N := n * wireMaxLeafWords with hN_def
  have hlW : wireMaxLeafWords = 64 := wireMaxLeafWords_val
  have hhW : wireMaxHeight = 32 := wireMaxHeight_val
  have hoW : openingWords = 193 := openingWords_val
  have hn256 : n ≤ 256 := hlen
  have hL := h.layout
  rw [query_eq]
  refine Keccak.Proof.wp_blk_append (WP.mono (queryHead_spec h hi (by omega) hr9 hr11) ?_
    fun s' ⟨hq, hrdi, hk⟩ ↦ ⟨hq, hrdi, fun a ha _ ↦ hk a ha⟩)
  rintro s₀ ⟨root, height, width, p, hpc, hgetq, hop, hl, hshape, hsim, hq4, hqh, hqw, hr13, hs0,
    K0, R0⟩
  show WP (.loop (.cmp .ne .r11 (.imm 0)) openOne) s₀ _ _
  have hpl8 : env.proof.openings.length ≤ 8 := h.decoded.2.2.2.1
  obtain ⟨-, -, -, -, -, hph⟩ := h.decoded
  obtain ⟨ph, pw, hph32, hpw64, -, -, -, -, hopn⟩ := hph p hpc
  have hph32' : ph ≤ 32 := hph32
  have hpw64' : pw ≤ 64 := hpw64
  set phase := env.proof.openings[p] with hphase
  have hgo : st.openings = phase :: env.proof.openings.drop (p + 1) := by
    rw [hop, List.drop_eq_getElem_cons hpc]
  have hdims : n ≠ 0 → height = ph ∧ width = pw := fun hn0 ↦ by
    have h0 : 0 < phase.length := by omega
    have := hshape hn0 _ (List.getElem_mem h0)
    exact ⟨by rw [← this.2, (hopn 0 h0).2.1], by rw [← this.1, (hopn 0 h0).1]⟩
  have hshapeAll : ∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height := by
    by_cases hn0 : n = 0
    · intro o ho
      have : phase = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at ho
      cases ho
    · exact hshape hn0
  -- the words the loop reads, kept
  have hrdi₀ : s₀.reg .rdi = env.ctx := hsim.rdi
  have hdec : ∀ (m : UInt64 → Option UInt64), Keep (fun a ↦ ClimbW env.ctx a ∨ InArea R N a) s₀.mem m →
      ∀ k < decodedWords env.L, m (wd env.dec k) = s.mem (wd env.dec k) := fun m hk k hkd ↦ by
    rw [hk _ ?_, K0 _ (hL.dec_not_foot hkd)]
    rintro (hc | ⟨k', hk', e⟩)
    · exact hL.dec_not_foot hkd (climbW_foot hc)
    · exact wd_ne_of_disj hfR hL.fitDec hRd hk' hkd e.symm
  have hctx : ∀ (m : UInt64 → Option UInt64), Keep (fun a ↦ ClimbW env.ctx a ∨ InArea R N a) s₀.mem m →
      ∀ k < ctxEnd, (k < scratchW ∨ (scratchW + Keccak.scratchWords ≤ k ∧ k < climbW) ∨ qRootW ≤ k) →
      m (wd env.ctx k) = s₀.mem (wd env.ctx k) := fun m hk k hkc hk' ↦ by
    rw [hk _ ?_]
    rintro (hc | ⟨k', hk'', e⟩)
    · exact ctx_not_climbW hk' (by lay_omega) hc
    · exact wd_ne_of_disj hfR hL.fitCtx hRc hk'' hkc e.symm
  have hwork : ∀ (m : UInt64 → Option UInt64), Keep (fun a ↦ ClimbW env.ctx a ∨ InArea R N a) s₀.mem m →
      ∀ k < workWords, m (wd env.work k) = s₀.mem (wd env.work k) := fun m hk k hkw ↦ by
    rw [hk _ ?_]
    rintro (hc | ⟨k', hk'', e⟩)
    · exact (hL.work_not_ctxIn (by lay_omega) hkw) (hc.elim (fun h ↦ h.mono (lo' := scratchW) (hi' := ctxEnd) le_rfl (by lay_omega))
        fun h ↦ h.mono (lo' := scratchW) (hi' := ctxEnd) (by lay_omega) (by lay_omega))
    · exact wd_ne_of_disj hfR hL.fitWork hRw hk'' hkw e.symm
  have hpos : ∀ (m : UInt64 → Option UInt64), Keep (fun a ↦ ClimbW env.ctx a ∨ InArea R N a) s₀.mem m →
      ∀ j (hj : j < n), m (wd P j) = some ps[j].toUInt64 := fun m hk j hj ↦ by
    rw [hk _ ?_, K0 _ ?_]
    · exact hP j hj
    · rintro (⟨k, -, hk', e⟩ | ⟨k, hk', e⟩)
      · exact wd_ne_of_disj hfP hL.fitCtx hPc hj hk' e
      · exact wd_ne_of_disj hfP hL.fitWork hPw hj hk' e
    · rintro (hc | ⟨k', hk'', e⟩)
      · obtain ⟨k, -, hk', e⟩ := hc.elim
          (fun h ↦ h.mono (lo' := scratchW) (hi' := ctxEnd) le_rfl (by lay_omega))
          fun h ↦ h.mono (lo' := scratchW) (hi' := ctxEnd) (by lay_omega) (by lay_omega)
        exact wd_ne_of_disj hfP hL.fitCtx hPc hj (show k < ctxEnd by lay_omega) e
      · exact wd_ne_of_disj hfR hfP hRP hk'' hj e.symm
  have hNfit : N ≤ 2 ^ 61 := by unfold Fits at hfR; have := R.toNat_lt; omega
  refine WP.loop (fun s' ↦ ∃ j, ∃ _ : j ≤ n, s'.reg .rdi = env.ctx ∧ s'.reg .r10 = wd P j ∧
      s'.reg .r11 = (n - j).toUInt64 ∧ s'.reg .r12 = wd R (j * width) ∧
      s'.reg .r13 = wd env.dec (phaseBase env.L p + 3 + j * openingWords) ∧
      (∀ k (hk : k < j), OpenOk root (ps[k]'(by omega)) (phase[k]'(by omega))) ∧
      (∀ k (hk : k < j), ∀ t < width, s'.mem (wd R (k * width + t)) =
        some ((phase[k]'(by omega)).leaf.getD t 0).lane) ∧
      Keep (fun a ↦ ClimbW env.ctx a ∨ InArea R N a) s₀.mem s'.mem ∧
      RegsFrame queryClobbers s₀ s' ∧ ∀ a, (s'.mem a).isSome = (s₀.mem a).isSome)
    (fun s' ↦ (s'.reg .r11).toNat)
    ⟨0, by omega, hrdi₀, by rw [R0 _ (by simp), hr10, wd_zero], by rw [R0 _ (by simp), hr11]; rfl,
      by rw [R0 _ (by simp), hr12, Nat.zero_mul, wd_zero], by rw [hr13, Nat.zero_mul, Nat.add_zero],
      fun k hk ↦ absurd hk (by omega), fun k hk ↦ absurd hk (by omega), Keep.refl _ _, rf_refl _ _,
      fun _ ↦ rfl⟩ ?_ ?_
  · rintro s' ⟨j, hj, h1, h10, h11, h12, h13, hok, hrow, hk, hr, hs⟩ hc
    have hjn : j < n := by
      rw [cond_ne, rhs_imm, h11, bne_iff_ne, ne_eq] at hc
      by_contra hh
      exact hc (by rw [show n - j = 0 by omega]; rfl)
    have hn0 : n ≠ 0 := by omega
    obtain ⟨hhe, hwe⟩ := hdims hn0
    have hjp : j < phase.length := by omega
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hopn j hjp
    have hob := opening_le (L := env.L) (p := p) (j := j) (by omega) (by omega)
    have hOk : phaseBase env.L p + 3 + j * openingWords < decodedWords env.L := by omega
    have hwid : j * width + width ≤ N := by
      rw [hN_def, hlW, hwe]
      have : (j + 1) * pw ≤ n * 64 := Nat.mul_le_mul (by omega) hpw64'
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    refine WP.mono (WP.frame (openOne_spec (ctx := env.ctx) (R := R) (n := N) (q := ps[j])
      (c := n - j) (root := root) (o := phase[j]) h1
      (hL.dom.of_isSome fun a ↦ (hs a).trans (hs0 a)) hL.fitCtx
      (fun k hk' ↦ by rw [hctx _ hk _ (by lay_omega) (.inr (.inr (by lay_omega)))]; exact hq4 k hk')
      (by rw [hctx _ hk _ (by lay_omega) (.inr (.inr (by lay_omega)))]; exact hqh)
      (by rw [hctx _ hk _ (by lay_omega) (.inr (.inr (by lay_omega)))]; exact hqw)
      (by rw [hhe]; exact hph32) (by rw [hwe]; exact hpw64) (by rw [o1, hwe]) (by rw [o2, hhe]) o3 h13
      (hL.fitDec.sub hOk (by omega)) (Disj.sub hL.fitDec hL.disjCD.symm hOk (by omega))
      (by rw [wd_shift, Nat.add_zero, hdec _ hk _ hOk]; exact o4)
      (fun t ht ↦ by rw [wd_shift, ← Nat.add_assoc, hdec _ hk _ (by omega)]; exact o5 t (by omega))
      (fun d hd l hl' ↦ by
        rw [wd_shift, show phaseBase env.L p + 3 + j * openingWords + (1 + wireMaxLeafWords + 4 * d + l) =
          phaseBase env.L p + 3 + j * openingWords + 1 + wireMaxLeafWords + 4 * d + l by omega,
          hdec _ hk _ (by omega)]
        exact o6 d (by omega) l hl')
      h10 (hpos _ hk j hjn) (hps _ (List.getElem_mem _)) h12 hwid hfR hRc
      (Disj.sub hL.fitDec hRd.symm hOk (by omega))
      (fun t ht ↦ by rw [hs, hs0]; exact hRs _ (by omega)) h11 (by omega) (by omega))) ?_ ?_
    · rintro s'' ⟨⟨hopen, hrow', hk', g10, g13, g12, g11, gr⟩, gs, -⟩
      refine ⟨⟨j + 1, by omega, by rw [gr _ (by simp [queryClobbers])]; exact h1,
        by rw [g10, add8_wd], by rw [g11, Nat.sub_sub], by rw [g12, Nat.add_mul, Nat.one_mul],
        by rw [g13, wd_shift, Nat.add_mul, Nat.one_mul, Nat.add_assoc], fun k hk'' ↦ ?_,
        fun k hk'' t ht ↦ ?_, hk.trans hk' (fun _ h ↦ h) ?_, rf_trans hr gr (fun _ h ↦ h) (fun _ h ↦ h),
        fun a ↦ (gs a).trans (hs a)⟩, ?_⟩
      · by_cases hkj : k < j
        · exact hok k hkj
        · have hkj' : j = k := by omega
          subst hkj'
          exact hopen
      · by_cases hkj : k < j
        · rw [hk' _ ?_]
          · exact hrow k hkj t ht
          rintro (hc | ⟨t', ht', e⟩)
          · exact not_climbW (fun k' hk' e ↦ wd_ne_of_disj hfR hL.fitCtx hRc
              (show k * width + t < N from row_lt (by omega) ht (by omega)) hk' e) hc
          · have h1 := row_lt (n := n) (W := wireMaxLeafWords) (show k < n by omega) ht (by omega)
            rw [wd_inj (by omega) (by omega)] at e
            have h2 := row_disj (t' := t') hkj ht
            omega
        · have hkj' : j = k := by omega
          subst hkj'
          exact hrow' t ht
      · rintro a (hc | ⟨t, ht, rfl⟩)
        · exact .inl hc
        · exact .inr ⟨_, by omega, rfl⟩
      · rw [g11, h11, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
        omega
    · rintro s'' ⟨⟨hbad, grdi, gk⟩, -, -⟩
      refine ⟨?_, grdi.trans h.rdi.symm, fun a ha hb ↦ ?_⟩
      · rw [queryStep_of hgetq hgo, openPhase_none_of_not hshapeAll ⟨j, hjn, hjp, hbad⟩]
        rfl
      · rw [gk a ?_, hk a ?_, K0 a ha]
        · rintro (hc | hc)
          · exact ha (climbW_foot hc)
          · exact hb hc
        · rintro (hc | ⟨t, ht, rfl⟩)
          · exact ha (climbW_foot hc)
          · exact hb ⟨_, by omega, rfl⟩
  · rintro s' ⟨j, hj, h1, h10, h11, h12, h13, hok, hrow, hk, hr, hs⟩ hc
    have hjn : j = n := by
      rw [cond_ne, rhs_imm, h11, bne_eq_false_iff_eq] at hc
      have := congrArg UInt64.toNat hc
      rw [toNat_toUInt64 (by omega), show (Int64.toUInt64 0).toNat = 0 from rfl] at this
      omega
    refine ⟨phase.map (·.leaf), { st with openings := env.proof.openings.drop (p + 1) }, ?_,
      hsim.congrW h1 hs (fun k hk' ↦ hctx _ hk k (by rcases hk' with h | h <;> lay_omega)
          (by rcases hk' with h | ⟨h, h'⟩
              · exact .inl h
              · exact .inr (.inl ⟨by lay_omega, by lay_omega⟩)))
        (fun k hkd ↦ (hdec _ hk k hkd).trans (K0 _ (hL.dec_not_foot hkd)).symm)
        (fun k hkw ↦ hwork _ hk k hkw),
      rowsAt_of (w := width) (fun r hr' ↦ by
          obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr'
          exact (hshapeAll o ho).1)
        (fun k hk' t ht ↦ by
          simp only [List.getElem_map]
          exact hrow k (by simp only [List.length_map] at hk'; omega) t ht),
      ⟨h1.trans h.rdi.symm, rf_trans R0 hr (by simp [queryClobbers]) (fun _ h ↦ h),
        fun a ha ↦ ?_⟩⟩
    · rw [queryStep_of hgetq hgo, openPhase_some hshapeAll hl fun k hk hk' ↦ hok k (by omega)]
      rfl
    · rw [hk a ?_, K0 a fun h ↦ ha (.inl h)]
      rintro (hc | hc)
      · exact ha (.inl (climbW_foot hc))
      · exact ha (.inr hc)


end NativeVm.Transcript
