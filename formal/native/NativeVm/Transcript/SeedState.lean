module

public import NativeVm.Transcript.Seed

/-!
# The seed's sponge and cursors

`seedState_spec`: with the IV in the scratch lanes `0..4` and the public input in the context's
words `4..8`, `seedState` leaves the sponge at `keccakF1600 (seedInput iv pub)`, nothing waiting and
no ground challenge. `seedCursors_spec`: `seedCursors` sets the cursors at the stream's and the
openings' starts and no roots.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

variable {env : Env} {s : QState} {P Q : QState → Prop}

theorem lane_seedInput (iv pub : Digest) {i : Nat} (hi : i < 25) :
    Keccak.lane (seedInput iv pub) i =
      if h : i < 4 then iv[i] else if h' : i < 8 then pub[i - 4] else 0 := by
  unfold seedInput
  rw [lane_ofFn _ hi]

/-- **The sponge's initial state.** -/
theorem seedState_spec {ctx : UInt64} {iv pub : Digest} (hrdi : s.reg .rdi = ctx)
    (hdom : Dom ctx s.mem) (hiv : ∀ k (hk : k < 4), s.mem (wd ctx (scratchW + k)) = some iv[k])
    (hpub : ∀ k (hk : k < 4), s.mem (wd ctx (ctxPublic + k)) = some pub[k]) :
    WP seedState s (fun s' ↦ SpongeAt s'.mem ctx ⟨keccakF1600 (seedInput iv pub), [], none⟩ ∧
      Keep (CtxIn ctx scratchW ctxEnd) s.mem s'.mem ∧ RegsFrame [.rax, .rcx, .r8] s s') Q := by
  unfold seedState
  refine wp_then' (copyCtx_spec (f := fun t ↦ pub.toList.getD t 0) hrdi (by lay_omega) (by lay_omega)
    (by lay_omega) (fun t ht ↦ by rw [hpub t ht]; simp [ht]) (fun t ht ↦ hdom _ (by lay_omega))) ?_
  rintro s₁ ⟨h₁, k₁, r₁⟩ d₁
  have hrdi₁ : s₁.reg .rdi = ctx := (r₁ _ (by simp)).trans hrdi
  have hdom₁ := hdom.of_isSome d₁
  refine wp_then' (zeroCtx_spec hrdi₁ (by lay_omega) (fun t ht ↦ hdom₁ _ (by lay_omega))) ?_
  rintro s₂ ⟨h₂, k₂, r₂⟩ d₂
  have hrdi₂ : s₂.reg .rdi = ctx := by rw [r₂]; exact hrdi₁
  have hdom₂ := hdom₁.of_isSome d₂
  refine wp_then' (permuteAt_spec (A := seedInput iv pub) hrdi₂ (fun k hk ↦ hdom₂ _ (by lay_omega))
    (fun i hi ↦ ?_)) ?_
  · rw [lane_seedInput _ _ hi]
    by_cases h4 : i < 4
    · simp only [h4, ↓reduceDIte]
      rw [k₂.ctx (by lay_omega) (by lay_omega) (by lay_omega),
        k₁.ctx (by lay_omega) (by lay_omega) (by lay_omega)]
      exact hiv i h4
    · simp only [h4, ↓reduceDIte]
      by_cases h8 : i < 8
      · simp only [h8, ↓reduceDIte]
        rw [k₂.ctx (by lay_omega) (by lay_omega) (by lay_omega)]
        have := h₁ (i - 4) (by omega)
        rw [show scratchW + 4 + (i - 4) = scratchW + i by omega] at this
        rw [this]
        simp [Vector.getElem_toList, show i - 4 < 4 by omega]
      · simp only [h8, ↓reduceDIte]
        have := h₂ (i - 8) (by omega)
        rwa [show scratchW + 8 + (i - 8) = scratchW + i by omega] at this
  rintro s₃ ⟨h₃, -, k₃, r₃⟩ d₃
  have hrdi₃ : s₃.reg .rdi = ctx := (r₃ _ (by simp)).trans hrdi₂
  have hdom₃ := hdom₂.of_isSome d₃
  refine wp_then' (copyCtx_spec (f := fun t ↦ Keccak.lane (keccakF1600 (seedInput iv pub)) t) hrdi₃
    (by lay_omega) (by lay_omega) (by lay_omega) (fun t ht ↦ h₃ t ht)
    (fun t ht ↦ hdom₃ _ (by lay_omega))) ?_
  rintro s₄ ⟨h₄, k₄, r₄⟩ d₄
  have hrdi₄ : s₄.reg .rdi = ctx := (r₄ _ (by simp)).trans hrdi₃
  have hdom₄ := hdom₃.of_isSome d₄
  refine wp_then' (zeroCtx_spec hrdi₄ (by lay_omega) (fun t ht ↦ hdom₄ _ (by lay_omega))) ?_
  rintro s₅ ⟨h₅, k₅, r₅⟩ d₅
  have hrdi₅ : s₅.reg .rdi = ctx := by rw [r₅]; exact hrdi₄
  have hdom₅ := hdom₄.of_isSome d₅
  refine wp_storei (eval_cw hrdi₅ _) (hdom₅.isSome (by lay_omega)) ?_
  refine wp_storei (eval_cw hrdi₅ _) (by some_tac) (wp_done ⟨⟨fun i hi ↦ ?_, by simp, ?_,
    fun i hi ↦ ?_, ?_⟩, ?_, ?_⟩)
  · mem_simp
    rw [k₅.ctx (by lay_omega) (by lay_omega) (by lay_omega)]
    exact h₄ i hi
  · mem_simp; rfl
  · mem_simp
    rw [h₅ i hi]
    simp [pendingLanes]
  · show _ = _
    mem_simp
  · have k : Keep (CtxIn ctx scratchW ctxEnd) s.mem s₅.mem :=
      ((((k₁.mono fun _ h ↦ h.mono (by lay_omega) (by lay_omega)).trans k₂ (fun _ h ↦ h)
        (fun _ h ↦ h.mono (by lay_omega) (by lay_omega))).trans k₃ (fun _ h ↦ h)
        (fun _ h ↦ h.mono (by lay_omega) (by lay_omega))).trans k₄ (fun _ h ↦ h)
        (fun _ h ↦ h.mono (by lay_omega) (by lay_omega))).trans k₅ (fun _ h ↦ h)
        (fun _ h ↦ h.mono (by lay_omega) (by lay_omega))
    exact (k.setMem (CtxIn.word (by lay_omega) (by lay_omega)) _).setMem
      (CtxIn.word (by lay_omega) (by lay_omega)) _
  · intro r hr
    rw [QState.setMem_reg, QState.setMem_reg, congrFun r₅ r, r₄ r (by simp_all), r₃ r hr,
      congrFun r₂ r, r₁ r (by simp_all)]

/-- `L` rounded down to a multiple of `16`, in bytes: the stream's words. -/
theorem shr4_shl4 {L : Nat} (hL : L < 2 ^ 64) :
    L.toUInt64 >>> (4 : Nat).toUInt64 <<< (4 : Nat).toUInt64 = (8 * (2 * (L / 16))).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, toNat_toUInt64 hL, toNat_toUInt64 (by omega),
    toNat_toUInt64 (by omega)]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- **The cursors**: the stream's and the openings' starts, no roots. -/
theorem seedCursors_spec {ctx : UInt64} (hrdi : s.reg .rdi = ctx) (hL : Layout env s.mem)
    (hctx : env.ctx = ctx) (hdec : Decoded s.mem env.dec env.L env.proof)
    (hLw : s.mem (wd ctx ctxWireLen) = some env.L.toUInt64) (hL64 : env.L < 2 ^ 64) :
    WP seedCursors s (fun s' ↦ s'.mem (wd env.work workCursor) = some (0 : Nat).toUInt64 ∧
      s'.mem (wd env.work workPhase) = some (0 : Nat).toUInt64 ∧
      s'.mem (wd env.work workPhasePtr) = some (wd env.dec (phaseBase env.L 0)) ∧
      s'.mem (wd env.work workPhaseCount) = some env.proof.openings.length.toUInt64 ∧
      s'.mem (wd env.work workRootCount) = some (0 : Nat).toUInt64 ∧
      Keep (Foot env) s.mem s'.mem ∧
      (∀ j < ctxEnd, s'.mem (wd ctx j) = s.mem (wd ctx j)) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧ RegsFrame [.rax, .rcx, .rdx, .r11] s s') Q := by
  subst hctx
  have hwd := hL.wdom
  have hfit := hL.fitDec
  have hdw := decodedWords_eq env.L
  have hfitn : 8 * decodedWords env.L ≤ 2 ^ 64 := by unfold Fits at hfit; omega
  obtain ⟨-, -, -, -, hpc, -⟩ := hdec
  unfold seedCursors
  refine wp_load (eval_cw hrdi _) hL.workPtr ?_
  refine wp_load (eval_cw (by reg_simp; exact hrdi) _) hL.decPtr ?_
  refine wp_storei (work_reg (env := env) (by reg_simp) _) (by wsome_tac) ?_
  refine wp_storei (work_reg (env := env) (by reg_simp) _) (by wsome_tac) ?_
  refine wp_storei (work_reg (env := env) (by reg_simp) _) (by wsome_tac) ?_
  have hdecw : ∀ i, i < decodedWords env.L → ∀ k, k < workWords → wd env.dec i ≠ wd env.work k :=
    fun i hi k hk ↦ wd_ne_of_disj hL.fitDec hL.fitWork hL.disjDW hi hk
  refine wp_load (eval_cw (by reg_simp; exact hrdi) _) (by
    simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_of_not (hL.work_ne_ctx (by lay_omega) (by lay_omega)).symm,
      ite_of_not (hL.work_ne_ctx (by lay_omega) (by lay_omega)).symm,
      ite_of_not (hL.work_ne_ctx (by lay_omega) (by lay_omega)).symm]
    exact hLw) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
  have hrax : ∀ t : QState, t.reg .rax = env.L.toUInt64 >>> (4 : Nat).toUInt64 <<< (4 : Nat).toUInt64 +
      env.dec → t.reg .rax = wd env.dec (2 * (env.L / 16)) := fun t h ↦ by
    rw [h, shr4_shl4 hL64, wd, UInt64.add_comm]
  refine wp_load (x := wd env.dec (streamEnd env.L)) (by
    rw [eval_at, hrax _ (by reg_simp), show ((8 : Int64)).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl,
      wd_add, streamEnd_eq]
    congr 1; omega) (by
    simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_of_not (hdecw _ (by rw [streamEnd_eq]; omega) _ (by lay_omega)),
      ite_of_not (hdecw _ (by rw [streamEnd_eq]; omega) _ (by lay_omega)),
      ite_of_not (hdecw _ (by rw [streamEnd_eq]; omega) _ (by lay_omega))]
    exact hpc) ?_
  refine wp_store (work_reg (env := env) (by reg_simp) _) (by wsome_tac) ?_
  refine wp_reg rfl (wp_store (work_reg (env := env) (by reg_simp) _) (by wsome_tac) ?_)
  refine wp_done_gen fun s' hs ↦ ?_
  subst hs
  refine ⟨by mem_simp; rfl, by mem_simp; rfl, ?_, by mem_simp, by mem_simp; rfl, by keep_tac,
    fun j hj ↦ ?_, fun a ↦ by wisSome_tac, by rf_tac⟩
  · mem_simp
    rw [shr4_shl4 hL64, phaseBase_eq]
    congr 1
    open scoped UInt64.CommRing in
    simp only [wd, Nat.mul_zero, Nat.add_zero, Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add,
      UInt64.ofNat_mul, UInt64.reduceOfNat]
    open scoped UInt64.CommRing in ring
  · simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm, ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm,
      ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm, ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm,
      ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm]


/-- A block from a state, the state named. -/
theorem wp_name {xs : List Stmt} (h : ∀ s', s = s' → WP (blk xs) s' P Q) : WP (blk xs) s P Q :=
  h s rfl

/-- `runProof`'s initial state from the seed. -/
abbrev initState (bc : List K) (pub : Digest) (π : Proof) : VerifierProgramState :=
  ⟨⟨Id.run (spongeSeedWith (m := Id) keccakF1600 bc pub), [], none⟩, π.stream, π.openings, []⟩

/-- **The seed**: `seed` ends in a state that simulates `runProof`'s initial state, writing the
registers of `clobbers` and the words of the footprint and of the hash input only. -/
theorem seed_spec {bcA : UInt64} {bc : List K} {pub : Digest} (h : SeedPre env bcA bc pub s) :
    WP seed s (fun s' ↦ SimState env (initState bc pub env.proof) s' ∧ RegsFrame clobbers s s' ∧
      ∀ a, ¬ Foot env a → ¬ BufIn env bc.length a → s'.mem a = s.mem a) Q := by
  set n := bc.length with hn
  have hL := h.layout
  have hn32 := h.bcSmall
  have hbufctx : ∀ i, i < n + 2 → ∀ j, j < ctxEnd → wd env.work i ≠ wd env.ctx j := fun i hi j hj ↦
    wd_ne_of_disj h.fitBuf hL.fitCtx h.disjBufCtx hi hj
  unfold seed
  refine wp_then' (seedBuffer_spec h) ?_
  rintro s₁ ⟨hb₁, hk₁, h9, h11, rf₁⟩ d₁
  have hctx₁ : ∀ j, j < ctxEnd → s₁.mem (wd env.ctx j) = s.mem (wd env.ctx j) := fun j hj ↦
    hk₁ _ fun k hk e ↦ hbufctx k hk j hj e.symm
  have hrdi₁ : s₁.reg .rdi = env.ctx := (rf₁ _ (by simp)).trans h.rdi
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_name fun s₂ hs₂ ↦ ?_))))
  have hrbx : s₂.reg .rbx = (8 * n + 9).toUInt64 := by
    rw [← hs₂]; reg_simp
    rw [h9, toUInt64_shl _ _ (by omega), show (9 : UInt64) = (9 : Nat).toUInt64 from rfl, toUInt64_add]
    congr 1
  have hrsi : s₂.reg .rsi = env.work := by rw [← hs₂]; reg_simp; exact h11
  have hrdi₂ : s₂.reg .rdi = env.ctx := by rw [← hs₂]; reg_simp; exact hrdi₁
  have hmem₂ : s₂.mem = s₁.mem := by rw [← hs₂]; rfl
  refine wp_then' (hashAt_spec (ws := seedWords bc) (len := 8 * n + 9) hrdi₂ (seedWords_holds bc) hrbx
    hn32 (fun i hi ↦ ?_) (fun k hk ↦ ?_) (fun i hi k hk ↦ ?_)) ?_
  · rw [hrsi, hmem₂, seedWords_length] at *
    rw [show env.work + (8 * i).toUInt64 = wd env.work i from rfl, hb₁ i hi,
      List.getD_eq_getElem _ _ (by rw [seedWords_length]; omega)]
  · rw [hmem₂, hctx₁ _ (by lay_omega)]
    exact hL.ctxSome _ (by lay_omega)
  · rw [hrsi]
    exact hbufctx i (by rw [seedWords_length] at hi; omega) _ (by lay_omega)
  rintro s₃ ⟨hiv, -, k₃, r₃⟩ d₃
  rw [seedWords_take] at hiv
  set iv := keccak256 (versionTag ++ bc.flatMap K.toBytes) with hiv_def
  have hrdi₃ : s₃.reg .rdi = env.ctx := (r₃ _ (by simp)).trans hrdi₂
  have hctx₃ : ∀ j, j < scratchW → s₃.mem (wd env.ctx j) = s.mem (wd env.ctx j) := fun j hj ↦ by
    rw [k₃.ctx (by omega) (by lay_omega) (by lay_omega), hmem₂, hctx₁ _ (by lay_omega)]
  have hdom₃ : Dom env.ctx s₃.mem := fun k hk ↦ by
    rw [d₃, hmem₂, d₁]; exact hL.ctxSome k hk
  refine wp_then' (seedState_spec (iv := iv) (pub := pub) hrdi₃ hdom₃ (fun k hk ↦ hiv k hk)
    (fun k hk ↦ by rw [hctx₃ _ (by lay_omega)]; exact h.pubWords k hk)) ?_
  rintro s₄ ⟨hsp₄, k₄, r₄⟩ d₄
  have hrdi₄ : s₄.reg .rdi = env.ctx := (r₄ _ (by simp)).trans hrdi₃
  have hctx₄ : ∀ j, j < scratchW → s₄.mem (wd env.ctx j) = s.mem (wd env.ctx j) := fun j hj ↦ by
    rw [k₄.ctx (by omega) (by lay_omega) (by lay_omega), hctx₃ j hj]
  have hsome₄ : ∀ a, (s₄.mem a).isSome = (s.mem a).isSome := fun a ↦ by
    rw [d₄, d₃, hmem₂, d₁]
  -- the words outside the buffer and the context's scratch are the input's
  have hout₄ : ∀ a, (∀ k < n + 2, a ≠ wd env.work k) → ¬ CtxIn env.ctx scratchW ctxEnd a →
      s₄.mem a = s.mem a := fun a h1 h2 ↦ by
    rw [k₄ a h2, k₃ a (fun h' ↦ h2 (h'.mono le_rfl (by lay_omega))), hmem₂, hk₁ a h1]
  have hL₄ : Layout env s₄.mem :=
    { hL with
      ctxSome := fun k hk ↦ by rw [hsome₄]; exact hL.ctxSome k hk
      workSome := fun k hk ↦ by rw [hsome₄]; exact hL.workSome k hk
      decPtr := by rw [hctx₄ _ (by lay_omega)]; exact hL.decPtr
      workPtr := by rw [hctx₄ _ (by lay_omega)]; exact hL.workPtr }
  have hdec₄ : Decoded s₄.mem env.dec env.L env.proof := Decoded.congr h.decoded fun i hi ↦
    hout₄ _ (fun k hk e ↦ wd_ne_of_disj h.fitBuf hL.fitDec h.disjBufDec hk hi e.symm)
      (fun ⟨k, _, hk, e⟩ ↦ wd_ne_of_disj hL.fitDec hL.fitCtx hL.disjCD.symm hi hk e)
  refine wp_then' (seedCursors_spec hrdi₄ hL₄ rfl hdec₄
    (by rw [hctx₄ _ (by lay_omega)]; exact h.wireLen) h.L64) ?_
  rintro s₅ ⟨c0, p0, pp, pc, rc, k₅, hctx₅, d₅', r₅⟩ d₅
  refine wp_done ⟨⟨(r₅ _ (by simp)).trans hrdi₄, hL₄.congr d₅' k₅,
    Decoded.congr hdec₄ fun _ hi ↦ k₅ _ (hL₄.dec_not_foot hi),
    hsp₄.congr fun j _ _ ↦ hctx₅ j (by lay_omega), ⟨0, Nat.zero_le _, c0, rfl⟩,
    ⟨0, Nat.zero_le _, p0, pp, rfl⟩, pc, Nat.zero_le _, rc, fun j hj ↦ absurd hj (by simp)⟩, ?_, ?_⟩
  · intro r hr
    have hr' : ∀ l : List Reg64, (∀ x ∈ l, x ∈ clobbers) → r ∉ l := fun l hl hm ↦ hr (hl r hm)
    rw [r₅ r (hr' _ (by decide)), r₄ r (hr' _ (by decide)), r₃ r (hr' _ (by decide)), ← hs₂]
    reg_simp
    have : r ≠ .rsi ∧ r ≠ .rbx := ⟨fun e ↦ hr (by simp [e, clobbers]), fun e ↦ hr (by simp [e, clobbers])⟩
    simp only [this.1, this.2, ↓reduceIte]
    exact rf₁ r (hr' _ (by decide))
  · intro a hf hb
    rw [k₅ a hf]
    exact hout₄ a (fun k hk e ↦ hb ⟨k, hk, e⟩) (fun h' ↦ hf (foot_ctx h' le_rfl le_rfl))

end NativeVm.Transcript
