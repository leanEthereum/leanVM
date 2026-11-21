module

public import Native.Sphincs.Layers
public import Native.Sphincs.Fors

/-!
# `body` verifies

`body_spec`: from a context holding `encode pk m sig`, `body` ends normally with `rax = 1` if
`verifyWithKeccak pk m sig` and `0` if not, and the callee-saved registers as they were. The
phases: `save`, `PK.seed` and the address's zero fields into the buffers (`init_ok`), the digest,
its index and its FORS leaves (`digest_ok`), `fors` (`fors_ok`), `layers` (`layers_ok`), `result`
(`result_ok`), `restore`; `verifyWithKeccak_eq` is the same composition.
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-! ## Saving and restoring -/

theorem save_ok (hI : Inv base V s) :
    WP save s (fun s' ↦ ∃ V', Inv base V' s' ∧ s'.reg = s.reg ∧
      (∀ k, (k < 88 ∨ 94 ≤ k) → V' k = V k) ∧
      V' 88 = s.reg .rbx ∧ V' 89 = s.reg .rbp ∧ V' 90 = s.reg .r12 ∧ V' 91 = s.reg .r13 ∧
      V' 92 = s.reg .r14 ∧ V' 93 = s.reg .r15) E := by
  have hctx : Context.ctxWords = 3200 := rfl
  unfold save
  rw [show (List.range 6).map (fun i ↦ I (.store (cw (saveWord + i)) (Context.calleeSaved.getD i .rbx))) =
    [I (.store (cw 88) .rbx), I (.store (cw 89) .rbp), I (.store (cw 90) .r12),
      I (.store (cw 91) .r13), I (.store (cw 92) .r14), I (.store (cw 93) .r15)] from rfl]
  refine blk_store_cw' hI (by omega) fun s1 h1 hs1 ↦ ?_
  refine blk_store_cw' h1 (by omega) fun s2 h2 hs2 ↦ ?_
  refine blk_store_cw' h2 (by omega) fun s3 h3 hs3 ↦ ?_
  refine blk_store_cw' h3 (by omega) fun s4 h4 hs4 ↦ ?_
  refine blk_store_cw' h4 (by omega) fun s5 h5 hs5 ↦ ?_
  refine blk_store_cw' h5 (by omega) fun s6 h6 hs6 ↦ WP.blk_nil ⟨_, h6, ?_, fun k hk ↦ ?_, ?_⟩
  · rw [hs6, hs5, hs4, hs3, hs2, hs1]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hs5, hs4, hs3, hs2, hs1]

theorem restore_ok (hI : Inv base V s) :
    WP restore s (fun s' ↦ s'.reg .rax = s.reg .rax ∧ s'.reg .rbx = V 88 ∧ s'.reg .rbp = V 89 ∧
      s'.reg .r12 = V 90 ∧ s'.reg .r13 = V 91 ∧ s'.reg .r14 = V 92 ∧ s'.reg .r15 = V 93) E := by
  have hctx : Context.ctxWords = 3200 := rfl
  unfold restore
  rw [show (List.range 6).map (fun i ↦ I (.load (Context.calleeSaved.getD i .rbx) (cw (saveWord + i)))) =
    [I (.load .rbx (cw 88)), I (.load .rbp (cw 89)), I (.load .r12 (cw 90)),
      I (.load .r13 (cw 91)), I (.load .r14 (cw 92)), I (.load .r15 (cw 93))] from rfl]
  refine blk_load_cw hI (by omega) ?_
  refine blk_load_cw (hI.setReg (by decide) _) (by omega) ?_
  refine blk_load_cw ((hI.setReg (by decide) _).setReg (by decide) _) (by omega) ?_
  refine blk_load_cw (((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _)
    (by omega) ?_
  refine blk_load_cw ((((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide)
    _).setReg (by decide) _) (by omega) ?_
  refine blk_load_cw (((((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide)
    _).setReg (by decide) _).setReg (by decide) _) (by omega) ?_
  exact WP.blk_nil (by simp [QState.setReg_reg])

/-! ## The buffers' heads -/

theorem init_ok (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey} {m : Message}
    {sig : Signature} (hin : ∀ i < inputWords, V (inp + i) = encode pk m sig i) :
    WP (blk [mv2 inp smallBuf, mv2 inp bigBuf, setField 1 0, setField 2 0]) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ Static pk m sig V' ∧
        (∀ k, k ≠ smallBuf → k ≠ smallBuf + 1 → k ≠ bigBuf → k ≠ bigBuf + 1 → k ≠ adrsRec + 1 →
          k ≠ adrsRec + 2 → V' k = V k) ∧ RegsFrame [.rax] s s') E := by
  have hctx : Context.ctxWords = 3200 := rfl
  have hinp : inp = 128 := rfl
  have hsb : smallBuf = 1280 := rfl
  have hbb : bigBuf = 1296 := rfl
  have har : adrsRec = 1200 := rfl
  unfold setField
  apply WP.blk_cons
  refine WP.mono (mv2_ok hI (src := inp) (dst := smallBuf) (by omega) (by omega) (by omega))
    (fun s1 ⟨h1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  apply WP.blk_cons
  refine WP.mono (mv2_ok h1 (src := inp) (dst := bigBuf) (by omega) (by omega) (by omega))
    (fun s2 ⟨h2, f2⟩ ↦ ?_) (fun _ h ↦ h)
  refine blk_storei_cw' h2 (by omega) fun s3 h3 hs3 ↦ ?_
  refine blk_storei_cw' h3 (by omega) fun s4 h4 hs4 ↦ ?_
  have h0 := hin 0 (by unfold inputWords; omega)
  have h1' := hin 1 (by unfold inputWords; omega)
  rw [Nat.add_zero] at h0
  refine WP.blk_nil ⟨_, h4, ⟨fun i hi ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun k k0 k1 k2 k3 k4 k5 ↦ ?_,
    fun r hr ↦ ?_⟩
  · unfold inputWords at hi
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      hin i (by unfold inputWords; omega)]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self, h0, encode_seed0]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
      h1', encode_seed1]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self, Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), h0, encode_seed0]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), h1', encode_seed1]
  · rw [Function.update_of_ne (by omega), Function.update_self]
    rfl
  · rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne k5, Function.update_of_ne k4, Function.update_of_ne k3,
      Function.update_of_ne k2, Function.update_of_ne k1, Function.update_of_ne k0]
  · rw [hs4, hs3, f2 r hr, f1 r hr]

/-! ## The digest -/

theorem mdHead_words {pk : _root_.Sphincs.PublicKey} {m : Message} {sig : Signature}
    {V' : Nat → UInt64} (hS : Static pk m sig V)
    (hmd : ∀ i < 10, V' (mdBuf + i) = V (inp + (i + 8) % 10)) :
    words V' mdBuf 10 = mdHead sig.randomizer pk.publicSeed pk.root m := by
  have h := fun i (hi : i < 10) ↦ (hmd i hi).trans (hS.input _ (by unfold inputWords; omega))
  simp only [words, mdHead, show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl,
    show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h 0 (by omega)]; exact encode_R0 pk m sig
  · rw [h 1 (by omega)]; exact encode_R1 pk m sig
  · rw [h 2 (by omega)]; exact encode_seed0 pk m sig
  · rw [h 3 (by omega)]; exact encode_seed1 pk m sig
  · rw [h 4 (by omega)]; exact encode_root0 pk m sig
  · rw [h 5 (by omega)]; exact encode_root1 pk m sig
  · rw [h 6 (by omega)]; exact encode_msg pk m sig (i := 0) (by omega)
  · rw [h 7 (by omega)]; exact encode_msg pk m sig (i := 1) (by omega)
  · rw [h 8 (by omega)]; exact encode_msg pk m sig (i := 2) (by omega)
  · rw [h 9 (by omega)]; exact encode_msg pk m sig (i := 3) (by omega)

theorem digest_ok (hb : Fits base) (hI : Inv base V s) {pk : _root_.Sphincs.PublicKey}
    {m : Message} {sig : Signature} (hS : Static pk m sig V) :
    WP (blk [digestInput, digestCalls, readIndex, blk ((List.range 24).map forsLeaf)]) s
      (fun s' ↦ ∃ V', Inv base V' s' ∧ Frame V V' ∧
        (∀ κ : ForsTreeIndex, V' (forsLeaves + κ.val) = (digestForsLeaves (Id.run
          (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk sig.randomizer m))
            κ).val.toUInt64) ∧
        s'.reg .r15 = (digestIndex (Id.run (Verification.messageDigest (m := Id)
          LeanVM.Semantics.keccakF1600 pk sig.randomizer m))).val.toUInt64 ∧
        s'.reg .rdi = s.reg .rdi) E := by
  have hsw : scratchWords = 84 := rfl
  have hmd : mdBuf = 1152 := rfl
  have hdg : dgst = 1168 := rfl
  have hfl : forsLeaves = 1176 := rfl
  have hbb : bigBuf = 1296 := rfl
  have hsb : smallBuf = 1280 := rfl
  have har : adrsRec = 1200 := rfl
  apply WP.blk_cons
  refine WP.mono (digestInput_ok hI) (fun s1 ⟨V1, h1, e1, d1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  have F1 : Frame V V1 := fun k hk ↦ e1 k (by unfold Kept at hk; omega)
  apply WP.blk_cons
  refine WP.mono (digestCalls_ok hb h1 (R := sig.randomizer) pk ⟨rfl, rfl⟩ (mdHead_words hS d1))
    (fun s2 ⟨V2, h2, e2, d2, f2⟩ ↦ ?_) (fun _ h ↦ h)
  have F2 : Frame V V2 := fun k hk ↦ by
    have hk' := hk
    unfold Kept at hk'
    rw [e2 k (by omega) (by omega) (by omega), F1 k hk]
  apply WP.blk_cons
  refine WP.mono (readIndex_ok h2 d2) (fun s3 ⟨m3, rdi3, r15, f3⟩ ↦ ?_) (fun _ h ↦ h)
  have h3 : Inv base V2 s3 := h2.frame m3 rdi3
  refine WP.mono (forsLeaves_ok h3 d2) (fun s4 ⟨V4, h4, e4, d4, f4⟩ ↦ ⟨V4, h4,
    fun k hk ↦ ?_, fun κ ↦ d4 κ.val κ.isLt, ?_, ?_⟩) (fun _ h ↦ h)
  · have hk' := hk
    unfold Kept at hk'
    rw [e4 k (by omega), F2 k hk]
  · rw [f4 .r15 (by simp), r15]
    exact congrArg Nat.toUInt64 (digestIndex_val pk sig.randomizer m).symm
  · rw [f4 .rdi (by simp), rdi3, f2 .rdi (by simp), f1 .rdi (by simp)]

/-! ## The body -/

theorem body_spec {s : QState} {pk : _root_.Sphincs.PublicKey} {m : Message} {sig : Signature}
    (hrdi : s.reg .rdi = base) (hctx : Context.At s.mem base)
    (hin : Context.InputAt s.mem base inputWords (encode pk m sig)) :
    WP body s (fun s' ↦ s'.reg .rax = (if verifyWithKeccak pk m sig then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, s'.reg r = s.reg r) (fun _ ↦ False) := by
  have hb : Fits base := hctx.fits
  have hctxw : Context.ctxWords = 3200 := rfl
  have hI : Inv base (fun k ↦ (s.mem (base + (8 * k).toUInt64)).getD 0) s := by
    refine ⟨hrdi, fun k hk ↦ ?_⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hctx.words k hk)
    rw [hv]
    rfl
  have hin' : ∀ i < inputWords, (fun k ↦ (s.mem (base + (8 * k).toUInt64)).getD 0) (inp + i) =
      encode pk m sig i := fun i hi ↦ by
    simp only
    rw [show 8 * (inp + i) = Context.inputOff + 8 * i by unfold inp Context.inputOff; omega,
      hin i hi]
    rfl
  unfold body
  apply WP.blk_cons
  refine WP.mono (save_ok hI) (fun s1 ⟨V1, h1, hs1, e1, v88, v89, v90, v91, v92, v93⟩ ↦ ?_)
    (fun _ h ↦ h)
  refine wp_blk_take_drop 4 (WP.mono (init_ok h1 (pk := pk) (m := m) (sig := sig)
    fun i hi ↦ by rw [e1 _ (by unfold inp inputWords at *; omega)]; exact hin' i hi)
    (fun s2 ⟨V2, h2, hS2, e2, f2⟩ ↦ ?_) (fun _ h ↦ h))
  have hsave : ∀ k, 88 ≤ k → k < 94 → V2 k = V1 k := fun k h1 h2 ↦ by
    unfold smallBuf bigBuf adrsRec at e2
    exact e2 k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hkept : ∀ k, 88 ≤ k → k < 94 → Kept k := fun k h1 h2 ↦ by unfold Kept mdBuf; omega
  refine wp_blk_take_drop 4 (WP.mono (digest_ok hb h2 hS2)
    (fun s3 ⟨V3, h3, F3, l3, r15, rdi3⟩ ↦ ?_) (fun _ h ↦ h))
  apply WP.blk_cons
  refine WP.mono (fors_ok hb h3 (hS2.frame F3) r15 l3)
    (fun s4 ⟨V4, h4, F4, k0, k1, f4⟩ ↦ ?_) (fun _ h ↦ h)
  apply WP.blk_cons
  refine WP.mono (layers_ok (idx := digestIndex (Id.run (Verification.messageDigest (m := Id)
    LeanVM.Semantics.keccakF1600 pk sig.randomizer m)))
    (d := Id.run (Verification.forsRecover (m := Id) LeanVM.Semantics.keccakF1600 pk.publicSeed
      (digestIndex (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk
        sig.randomizer m)))
      (digestForsLeaves (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600
        pk sig.randomizer m))) sig.forsOpening))
    hb h4 ((hS2.frame F3).frame F4) k0 k1 (by rw [f4 .r15 (by simp), r15]))
    (fun s5 ⟨V5, h5, F5, hnone, hsome, f5⟩ ↦ ?_) (fun _ h ↦ h)
  apply WP.blk_cons
  refine WP.mono (result_ok h5 (((hS2.frame F3).frame F4).frame F5) hnone hsome)
    (fun s6 ⟨m6, rax6, f6⟩ ↦ ?_) (fun _ h ↦ h)
  have h6 : Inv base V5 s6 := h5.frame m6 (f6 .rdi (by simp))
  have F : Frame V2 V5 := F3.trans (F4.trans F5)
  refine WP.mono (restore_ok h6) (fun s7 ⟨rax7, r88, r89, r90, r91, r92, r93⟩ ↦ ⟨?_, ?_⟩)
    (fun _ h ↦ h)
  · rw [rax7, rax6, verifyWithKeccak_eq, ← layersAcc_three]
    generalize layersAcc _ _ _ _ 3 = o
    cases o <;> rfl
  · have hV : ∀ k, 88 ≤ k → k < 94 → V5 k = V1 k := fun k h1 h2 ↦ by
      rw [F k (hkept k h1 h2), hsave k h1 h2]
    intro r hr
    simp only [Context.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r88, hV 88 (by omega) (by omega), v88]
    · rw [r89, hV 89 (by omega) (by omega), v89]
    · rw [r90, hV 90 (by omega) (by omega), v90]
    · rw [r91, hV 91 (by omega) (by omega), v91]
    · rw [r92, hV 92 (by omega) (by omega), v92]
    · rw [r93, hV 93 (by omega) (by omega), v93]

end Native.SphincsVerifier
