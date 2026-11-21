module

public import NativeVm.Code.Phase3.TailBase
public import NativeVm.Code.Phase3.Pieces

/-!
# Phase 3 after the transcript: the lengths, the constants, `indexMle`, `g^(2^logBytecode − 1)`

`tl_imle`: `imleAt i dst`'s body, `indexMle` of the first `lenW i` coordinates of the GKR point into
`dst`. `tl_vals1`: `tailCode`'s first seven parts, the two lengths, `1`, `g`, `g²`, `0`, the two
`indexMle`s and the program counter's final value in their slots (`TlV1`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-- A region inside `tlW` is one phase 3 may write. -/
theorem tl_ok3 {r : Region} (h : ∃ q ∈ tlW, Within r q) : Ok3 r := by
  obtain ⟨q, hq, hw⟩ := h
  have := tl_ok q hq
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨le_trans h1 hw.1, le_trans hw.2 h2⟩
  · exact .inr (.inl ⟨le_trans h1 hw.1, le_trans hw.2 h2⟩)
  · exact .inr (.inr ⟨le_trans h1 hw.1, le_trans hw.2 h2⟩)

/-- **`imleAt i dst`'s body**: `indexMle` of the first `len` coordinates of the point into `dst`,
slots `8 .. 11` and `dst` written. -/
theorem tl_imle {i dst len : Nat} {point : Array EW} (hrdi : s.reg .rdi = env.ctx)
    (hwp : s.mem (wd env.ctx ctxWork) = some env.work) (hi : Inputs env inp s.mem)
    (hpt : EWArr s.mem (wd env.work 52704) point) (hps : point.size < 64)
    (hl : NatAt s.mem (wd env.work (lenW i)) len) (hlen : len ≤ point.size)
    (hone : EWAt s.mem (wd env.work sOne) 1) (hd' : dst + 2 ≤ sl 8) :
    WP (blk [I (.load .r14 (cw ctxWork)), I (.load .r15 (at_ .r14 (wdisp (lenW i)))),
        I (.mov .r13 .r14), I (.addi .r13 (wdisp pointR.off)), imleCode dst]) s
      (fun s' ↦ EWAt s'.mem (wd env.work dst) (indexMle (point.extract 0 len)) ∧
        Wrote env [⟨sl 8, 8⟩, ⟨dst, 2⟩] s s') E := by
  have hvs := valsR_stop
  have hvo := valsR_off
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine wp_load (eval_work (by rsimp) _) hl.2 ?_
  refine wp_reg rfl (wp_reg rfl ?_)
  refine WP.blk_cons (WP.mono (imle_spec (pt := point) (a := 52704) (n := len) (dst := dst) hlen
    (by rsimp) (by rsimp; rw [pc_pointR_off]; rfl) (by rsimp) hpt hone
    (by left; unfold sl; omega) (by omega) (by unfold sl at hd'; omega)
    (fun k h1 h2 ↦ hi.ok3_some' valsR_ok (a := k) (by unfold sl at h2; omega))
    ⟨hi.ok3_some' valsR_ok (a := dst) (by unfold sl at hd'; omega),
      hi.ok3_some' valsR_ok (a := dst + 1) (by unfold sl at hd'; omega)⟩) ?_ fun _ h ↦ h)
  rintro s' ⟨hE, hfr, hdom, hrf⟩
  refine WP.blk_nil ⟨hE, ⟨by rw [hrf .rdi (by decide)]; rsimp, fun a ha ↦ ?_, hdom⟩⟩
  refine hfr a (fun k h1 h2 e ↦ ha ⟨sl 8, 8⟩ (by simp) ⟨k - sl 8, show k - sl 8 < 8 by
    unfold sl at *; omega, by rw [e]; show wd env.work k = wd env.work (sl 8 + (k - sl 8))
                              rw [Nat.add_sub_cancel' h1]⟩)
    (fun e ↦ ha ⟨dst, 2⟩ (by simp) ⟨0, show 0 < 2 by decide, by rw [e]; rfl⟩)
    (fun e ↦ ha ⟨dst, 2⟩ (by simp) ⟨1, show 1 < 2 by decide, by rw [e]⟩)

/-- What `tailCode`'s first seven parts leave in phase 3's slots. -/
structure TlV1 (env : Env) (layout : LayoutW) (point : Array EW) (s : QState) : Prop where
  hone : EWAt s.mem (wd env.work sOne) 1
  hgen : EWAt s.mem (wd env.work sGen) gen
  hg2 : EWAt s.mem (wd env.work sG2) (gen * gen)
  hzero : EWAt s.mem (wd env.work sZero) 0
  him : EWAt s.mem (wd env.work sIm) (indexMle (point.extract 0 (min layout.logMemory point.size)))
  hib : EWAt s.mem (wd env.work sIb)
    (indexMle (point.extract 0 (min layout.logBytecode point.size)))
  hpc : EWAt s.mem (wd env.work sPc) (gpow (2 ^ layout.logBytecode - 1))
  hl0 : NatAt s.mem (wd env.work (lenW 0)) (min layout.logMemory point.size)
  hl1 : NatAt s.mem (wd env.work (lenW 1)) (min layout.logBytecode point.size)

/-- **The lengths, the constants, the two `indexMle`s, the program counter's final value.** -/
theorem tl_vals1 {layout : LayoutW} {rate : Nat} {point weights trees memory : Array EW}
    {beta mf bf share : EW} {xs : List Stmt} {P : QState → Prop}
    (h : TlIn env inp layout rate point weights trees memory beta mf bf share s)
    (hps : point.size < 64) (hws : weights.size = 16) (hts : trees.size = 3) (hms : memory.size = 2)
    (k : ∀ s', Wrote env tlW s s' → TlV1 env layout point s' → WP (blk xs) s' P E) :
    WP (blk (lensCode :: I (.load .r14 (cw ctxWork)) :: opsCode constOps ::
      blk [I (.load .r14 (cw ctxWork)), I (.load .r15 (at_ .r14 (wdisp (lenW 0)))),
        I (.mov .r13 .r14), I (.addi .r13 (wdisp pointR.off)), imleCode sIm] ::
      blk [I (.load .r14 (cw ctxWork)), I (.load .r15 (at_ .r14 (wdisp (lenW 1)))),
        I (.mov .r13 .r14), I (.addi .r13 (wdisp pointR.off)), imleCode sIb] ::
      I (.load .r14 (cw ctxWork)) :: pcCode :: xs)) s P E := by
  have hb := tl_stop
  -- the lengths
  refine wp_then (lensCode_spec (d := point.size) h.rdi h.wp h.hin h.lay (by rw [Region.at, pc_depthR_off]; exact h.depth))
    fun s1 ⟨l0, l1, w1', _⟩ ↦ ?_
  have w1 : Wrote env tlW s s1 := tl_widen w1' (by decide)
  have h1 := h.keep hps hws hts hms w1
  -- the constants
  refine wp_load (eval_cw h1.rdi ctxWork) h1.wp ?_
  refine wp_then (tl_ops_wrote constOps (S := []) (v := fun _ ↦ 0) (ws := [⟨52880, 26⟩])
    (fun r hr ↦ tl_ok3 (by rw [List.mem_singleton.mp hr]; decide)) h1.hin (by rsimp)
    (fun _ h ↦ absurd h (by simp)) (by simp) (by decide) (by decide)) fun s2 ⟨H2, w2', _⟩ ↦ ?_
  have w2 : Wrote env tlW s s2 := w1.trans (tl_widen (tl_pre w2' (by decide)) (by decide))
  have h2 := h.keep hps hws hts hms w2
  obtain ⟨c1, c2, c3, c4⟩ := constOps_run (fun _ ↦ 0)
  have one2 : EWAt s2.mem (wd env.work sOne) 1 := c1 ▸ H2 sOne (by decide)
  have gen2 : EWAt s2.mem (wd env.work sGen) gen := c2 ▸ H2 sGen (by decide)
  have g22 : EWAt s2.mem (wd env.work sG2) (gen * gen) := c3 ▸ H2 sG2 (by decide)
  have zero2 : EWAt s2.mem (wd env.work sZero) 0 := c4 ▸ H2 sZero (by decide)
  have w2'' := tl_pre w2' (by decide)
  have l02 := tl_natAt w2'' (by decide) (by decide) (by decide) l0
  have l12 := tl_natAt w2'' (by decide) (by decide) (by decide) l1
  -- `indexMle` of the memory's prefix
  refine wp_then (tl_imle h2.rdi h2.wp h2.hin h2.pt hps l02 (Nat.min_le_right _ _) one2
    (by decide)) fun s3 ⟨im3, w3'⟩ ↦ ?_
  have w3 : Wrote env tlW s s3 := w2.trans (tl_widen w3' (by decide))
  have h3 := h.keep hps hws hts hms w3
  have one3 := tl_ewat w3' (by decide) (by decide) (by decide) one2
  -- `indexMle` of the bytecode's prefix
  refine wp_then (tl_imle h3.rdi h3.wp h3.hin h3.pt hps
    (tl_natAt w3' (by decide) (by decide) (by decide) l12) (Nat.min_le_right _ _) one3
    (by decide)) fun s4 ⟨ib4, w4'⟩ ↦ ?_
  have w4 : Wrote env tlW s s4 := w3.trans (tl_widen w4' (by decide))
  have h4 := h.keep hps hws hts hms w4
  -- `g^(2^logBytecode − 1)`
  refine wp_load (eval_cw h4.rdi ctxWork) h4.wp ?_
  have hlb : NatAt s4.mem (wd env.work (layoutR.off + 1)) layout.logBytecode := by
    have := h4.lay.logBytecode; rwa [Region.at, wd_wd] at this
  have gen4 := tl_ewat w4' (by decide) (by decide) (by decide)
    (tl_ewat w3' (by decide) (by decide) (by decide) gen2)
  refine wp_then (pcCode_spec (by rsimp) h4.hin hlb h4.lay.logBytecodeBound gen4)
    fun s5 ⟨pc5, w5', _⟩ ↦ ?_
  have w45 : Wrote env [⟨sPc, 2⟩] s4 s5 := tl_pre w5' (by decide)
  have w5 : Wrote env tlW s s5 := w4.trans (tl_widen w45 (by decide))
  refine k s5 w5 ⟨?_, ?_, ?_, ?_, ?_, ?_, pc5, ?_, ?_⟩
  · exact tl_ewat w45 (by decide) (by decide) (by decide)
      (tl_ewat w4' (by decide) (by decide) (by decide) one3)
  · exact tl_ewat w45 (by decide) (by decide) (by decide) gen4
  · exact tl_ewat w45 (by decide) (by decide) (by decide)
      (tl_ewat w4' (by decide) (by decide) (by decide)
        (tl_ewat w3' (by decide) (by decide) (by decide) g22))
  · exact tl_ewat w45 (by decide) (by decide) (by decide)
      (tl_ewat w4' (by decide) (by decide) (by decide)
        (tl_ewat w3' (by decide) (by decide) (by decide) zero2))
  · exact tl_ewat w45 (by decide) (by decide) (by decide)
      (tl_ewat w4' (by decide) (by decide) (by decide) im3)
  · exact tl_ewat w45 (by decide) (by decide) (by decide) ib4
  · exact tl_natAt w45 (by decide) (by decide) (by decide)
      (tl_natAt w4' (by decide) (by decide) (by decide)
        (tl_natAt w3' (by decide) (by decide) (by decide) l02))
  · exact tl_natAt w45 (by decide) (by decide) (by decide)
      (tl_natAt w4' (by decide) (by decide) (by decide)
        (tl_natAt w3' (by decide) (by decide) (by decide) l12))

end NativeVm.Code.P3
