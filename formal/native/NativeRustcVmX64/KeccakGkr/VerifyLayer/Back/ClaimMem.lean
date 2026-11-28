module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.ClaimValue
public import NativeRustcVm.Layout.RepLemmas

/-! # Preserving the tail's live memory while writing the claim -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea tstateBytes off)

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW}

theorem claim_not_t (hpre : VerifyLayerPre a s c m0) {q : BitVec 64}
    (hq : InRange (cA m0) 768 q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have g := geo_of hpre
  have hn := g.hc
  have ht := g.ht
  have ha := g.htc
  have hd := pre_apart hpre (w := ⟨cA m0, 768⟩) (by simp) (r := a.region) (by simp)
  have hdn := (pre_rok hpre (r := a.region) (by simp)).2
  simp only [NativeRustcVm.Transcript.DecArea.region] at hd hdn
  rw [Sym.inRange_iff hn] at hq
  constructor
  · intro h'
    change InRange (tA m0) 760 q at h'
    rw [Sym.inRange_iff ht] at h'
    change (tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760 at h'
    omega
  · intro h'
    rw [Sym.inRange_iff hdn] at h'
    omega

theorem claim_not_scratch (hpre : VerifyLayerPre a s c m0) {o n : Nat} (hon : o + n ≤ 205824)
    {q : BitVec 64} (hq : InRange (cA m0) 768 q) :
    ¬InRange (sA m0 + BitVec.ofNat 64 o) n q := by
  have g := geo_of hpre
  have hc := g.hc
  have hs := g.hs
  have ha := g.hcsc
  by_cases hn : n = 0
  · subst hn; unfold InRange; omega
  intro h'
  rw [Sym.inRange_iff hc] at hq
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at h'
  omega

theorem TailLive.claim (hpre : VerifyLayerPre a s c m0) {d d' : DataMem}
    (h : TailLive m0 a c ch b pt lp t s6 d) (hpt : pt.size ≤ 30)
    (hf : FrSame m0 d d' 24 1944) (hk : Kept d d')
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 3232) 3232 q ∨ InRange (cA m0) 768 q)) :
    TailLive m0 a c ch b pt lp t s6 d' := by
  have g := geo_of hpre
  refine ⟨h.ts.frame hk (fun q hq ↦ hq.elim
      (fun hq ↦ (ctx hpre (F := 2000) (by decide)).stack_not_t hq)
      (fun hq ↦ claim_not_t hpre hq)) hs,
    FWs.keepR (os := [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200])
      rfl hf (by decide +kernel) h.fw,
    (hf.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hf.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.pt
      (by rw [Array.length_toList]; omega), ?_⟩
  apply NativeRustcVm.BytesAt.of_sameOutside h.weights hs
  intro i hi hq
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList,
    NativeRustcVm.KeccakGkr.linearTranspose_size'] at hi
  have hq' : InRange (sA m0 + BitVec.ofNat 64 25600) 25600
      (lA m0 + BitVec.ofNat 64 i) := NativeRustcVm.Transcript.inRange_off_self hi (by decide)
  rcases hq with hq | hq
  · have hn := g.hN
    have htop := g.top
    have ha := g.hss
    have hsc := g.hs
    rw [Sym.inRange_iff (by rw [g.sbN]; omega), g.sbN] at hq
    rw [Sym.inRange_iff (by rw [g.sa (by decide)]; omega), g.sa (by decide)] at hq'
    omega
  · exact claim_not_scratch hpre (by decide) hq hq'

omit [Labels] in
theorem hexClaim {d : MachineData} {ret : BitVec 64} {S : SState} {extra : List (BitVec 64 × Nat)}
    (g : Geo m0)
    (h : S.mem.all (fun w ↦ w.r == 0 || (w.r == 1 && decide (w.off + w.n ≤ 768))) = true) :
    ∀ w ∈ S.mem, w.r ≠ 0 → ∀ p n,
      (envB m0 d ((cA m0, 768) :: extra) (fun _ ↦ 0) ret).regions[w.r]? = some (p, n) →
      ∀ q, p.toNat + w.off ≤ q.toNat → q.toNat < p.toNat + w.off + w.n → InRange (cA m0) 768 q := by
  intro w hw hr p n he q h1 h2
  have hh := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
  rcases hh with hh | ⟨hh, hn⟩
  · exact (hr hh).elim
  · rw [hh] at he
    change some (cA m0, 768) = some (p, n) at he
    cases he
    rw [Sym.inRange_iff g.hc]
    omega

theorem claim_same (hpre : VerifyLayerPre a s c m0) {d d' : DataMem} {o n p len : Nat}
    (hon : o + n ≤ 768) (hpl : p + len ≤ 768) (hap : p + len ≤ o ∨ o + n ≤ p)
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 3232) 3232 q ∨
      InRange (cA m0 + BitVec.ofNat 64 o) n q)) :
    NativeRustcVm.Layout.Same d d' (cA m0 + BitVec.ofNat 64 p) len := by
  have g := geo_of hpre
  have hn := g.hN
  have ht := g.top
  have hc := g.hc
  have hcs := g.hcs
  apply NativeRustcVm.Layout.Same.of_sameOutside hs
  intro i hi hq
  have he : (cA m0 + BitVec.ofNat 64 p + BitVec.ofNat 64 i).toNat =
      (cA m0).toNat + p + i := by
    rw [NativeRustcVm.addr_add_add, g.ca (by omega)]
    omega
  rcases hq with hq | hq
  · rw [Sym.inRange_iff (by rw [g.sbN]; omega), g.sbN, he] at hq
    omega
  · by_cases hzero : n = 0
    · subst hzero; unfold InRange at hq; omega
    · rw [Sym.inRange_iff (by rw [g.ca (by omega)]; omega), g.ca (by omega), he] at hq
      omega

omit [Labels] in
theorem hexClaimRange {d : MachineData} {ret : BitVec 64} {S : SState}
    (g : Geo m0) {o n : Nat} (ho : o < 768) (hon : o + n ≤ 768)
    (h : S.mem.all (fun w ↦ w.r == 0 ||
      (w.r == 1 && decide (o ≤ w.off ∧ w.off + w.n ≤ o + n))) = true) :
    ∀ w ∈ S.mem, w.r ≠ 0 → ∀ p sz,
      (envB m0 d [(cA m0, 768)] (fun _ ↦ 0) ret).regions[w.r]? = some (p, sz) →
      ∀ q, p.toNat + w.off ≤ q.toNat → q.toNat < p.toNat + w.off + w.n →
        InRange (cA m0 + BitVec.ofNat 64 o) n q := by
  intro w hw hr p sz he q h1 h2
  have hh := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
  rcases hh with hh | ⟨hh, hlo, hhi⟩
  · exact (hr hh).elim
  · rw [hh] at he
    change some (cA m0, 768) = some (p, sz) at he
    cases he
    have hc := g.hc
    rw [Sym.inRange_iff (by rw [g.ca ho]; omega), g.ca ho]
    omega

omit [Labels] in
theorem claim_subrange (g : Geo m0) {o n : Nat} (hon : o + n ≤ 768)
    {q : BitVec 64} (hq : InRange (cA m0 + BitVec.ofNat 64 o) n q) :
    InRange (cA m0) 768 q := by
  by_cases hz : n = 0
  · subst hz; unfold InRange at hq; omega
  have hc := g.hc
  rw [Sym.inRange_iff (by rw [g.ca (by omega)]; omega), g.ca (by omega)] at hq
  rw [Sym.inRange_iff hc]
  omega

theorem claim_not_fr (hpre : VerifyLayerPre a s c m0) {q : BitVec 64}
    (hq : InRange (cA m0) 768 q) :
    ¬InRange (stackBelow m0 2016) 2024 q := by
  have g := geo_of hpre
  have hc := g.hc
  have hcs := g.hcs
  have hn := g.hN
  have ht := g.top
  rw [Sym.inRange_iff hc] at hq
  intro hf
  rw [Sym.inRange_iff (by rw [g.fbN]; omega), g.fbN] at hf
  omega

theorem TailLive.claimBlk (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    (h : TailLive m0 a c ch b pt lp t s6 d.dmem) (hpt : pt.size ≤ 30)
    {ret : BitVec 64} {S : SState} {extra : List (BitVec 64 × Nat)}
    (hwf : (envB m0 d ((cA m0, 768) :: extra) (fun _ ↦ 0) ret).WF)
    (hm : Match (envB m0 d ((cA m0, 768) :: extra) (fun _ ↦ 0) ret) S d')
    (hbr : belowRet 2016 S = true) (hin : writesIn S = true)
    (hmiss : missB 24 1944 S = true)
    (hex : S.mem.all (fun w ↦ w.r == 0 || (w.r == 1 && decide (w.off + w.n ≤ 768))) = true) :
    TailLive m0 a c ch b pt lp t s6 d'.dmem :=
  h.claim hpre hpt (frSame_blk hwf hm hin (by decide) hmiss) (hm.kept hwf)
    (NativeRustcVm.SameOutside.mono (hm.sameOutside hwf)
      fun _ hq ↦ written_chg (geo_of hpre) hbr (hexClaim (geo_of hpre) hex) hq)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
