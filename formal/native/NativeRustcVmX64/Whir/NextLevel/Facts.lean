module

public import NativeRustcVmX64.Whir.NextLevel.Mid

/-!
# `next_level`: the frame's facts, calls from any offset (x86-64)

The values the body keeps in its frame from `b13` on: the out-of-domain value, the high part and
the out-of-domain point (`FV`, in `ZoneV`: `[128, 144)` and `[176, 760)`), with `λ` (`FF`, in
`Zone`: also `[88, 104)`). A block whose writes are in `Gap` ranges (`keepZ_blk`) or a call
changing a `Gap` range of the frame (`keepZ_call`) keeps them. A call from RSP offset `o` keeps `K`
(`Ctx.K_callO`) and the bytes apart from its changes (`Ctx.same_call`); a block changing frame
bytes from `760` and RCX only keeps `K` (`Ctx.K_low`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

@[expose] public section

/-- The frame's bytes holding the out-of-domain value, the high part and point. -/
def ZoneV (j : Nat) : Prop := (128 ≤ j ∧ j < 144) ∨ (176 ≤ j ∧ j < 760)

/-- The frame's bytes holding the facts: also `λ`. -/
def Zone (j : Nat) : Prop := (88 ≤ j ∧ j < 104) ∨ ZoneV j

/-- A write range `[p.1, p.2)` of the frame missing `Zone`. -/
def Gap (p : Nat × Nat) : Prop :=
  p.2 ≤ 88 ∨ (104 ≤ p.1 ∧ p.2 ≤ 128) ∨ (144 ≤ p.1 ∧ p.2 ≤ 176) ∨ 760 ≤ p.1

instance (p : Nat × Nat) : Decidable (Gap p) := by unfold Gap; infer_instance

/-- A write range `[p.1, p.2)` of the frame missing `ZoneV`. -/
def GapV (p : Nat × Nat) : Prop := p.2 ≤ 128 ∨ (144 ≤ p.1 ∧ p.2 ≤ 176) ∨ 760 ≤ p.1

instance (p : Nat × Nat) : Decidable (GapV p) := by unfold GapV; infer_instance

/-- `ZoneV`'s bytes kept. -/
def KeepV (m0 : MachineData) (d d' : Mem 64) : Prop :=
  ∀ j, ZoneV j → d'.get? (loc m0 j) = d.get? (loc m0 j)

/-- `Zone`'s bytes kept. -/
def KeepZ (m0 : MachineData) (d d' : Mem 64) : Prop :=
  ∀ j, Zone j → d'.get? (loc m0 j) = d.get? (loc m0 j)

/-- The out-of-domain value (`136`, `128`), the high part (`176`), `μ` and the out-of-domain
point (`272`, `280`). -/
structure FV (m0 : MachineData) (xs ood : Array EW) (v : EW) (d : Mem 64) : Prop where
  v1 : NativeRustcVm.WordAt d (loc m0 128) v.c1
  v0 : NativeRustcVm.WordAt d (loc m0 136) v.c0
  high : NativeRustcVm.EWsAt d (loc m0 176) xs.toList
  oodN : NativeRustcVm.WordAt d (loc m0 272) (.ofBitVec (reg m0 .r9))
  oodp : NativeRustcVm.EWsAt d (loc m0 280) ood.toList

/-- `FV` and `λ` (`96`, `88`). -/
structure FF (m0 : MachineData) (xs ood : Array EW) (v lam : EW) (d : Mem 64) : Prop where
  fv : FV m0 xs ood v d
  l1 : NativeRustcVm.WordAt d (loc m0 88) lam.c1
  l0 : NativeRustcVm.WordAt d (loc m0 96) lam.c0

end

public section

theorem KeepZ.v {m0 : MachineData} {d d' : Mem 64} (h : KeepZ m0 d d') : KeepV m0 d d' :=
  fun j hj ↦ h j (Or.inr hj)

theorem KeepZ.trans {m0 : MachineData} {d d' d'' : Mem 64} (h : KeepZ m0 d d')
    (h' : KeepZ m0 d' d'') : KeepZ m0 d d'' := fun j hj ↦ (h' j hj).trans (h j hj)

theorem KeepZ.of_eq {m0 : MachineData} {d d' : Mem 64} (h : d' = d) : KeepZ m0 d d' :=
  fun _ _ ↦ by rw [h]

theorem KeepV.trans {m0 : MachineData} {d d' d'' : Mem 64} (h : KeepV m0 d d')
    (h' : KeepV m0 d' d'') : KeepV m0 d d'' := fun j hj ↦ (h' j hj).trans (h j hj)

theorem KeepV.of_eq {m0 : MachineData} {d d' : Mem 64} (h : d' = d) : KeepV m0 d d' :=
  fun _ _ ↦ by rw [h]

theorem bytes_keep {m0 : MachineData} {d d' : Mem 64} {Z : Nat → Prop}
    (hk : ∀ j, Z j → d'.get? (loc m0 j) = d.get? (loc m0 j)) {j : Nat} {bs : List UInt8}
    (hz : ∀ i < bs.length, Z (j + i)) (h : NativeRustcVm.BytesAt d (loc m0 j) bs) :
    NativeRustcVm.BytesAt d' (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hk _ (hz i hi)]
  exact this

theorem FV.keep {m0 : MachineData} {xs ood : Array EW} {v : EW} {d d' : Mem 64}
    (h : FV m0 xs ood v d) (hk : KeepV m0 d d') (hx : xs.size ≤ 6) (ho : ood.size ≤ 30) :
    FV m0 xs ood v d' :=
  ⟨bytes_keep hk (fun i hi ↦ by
      simp only [NativeRustcVm.length_wordBytes] at hi; unfold ZoneV; omega) h.v1,
    bytes_keep hk (fun i hi ↦ by
      simp only [NativeRustcVm.length_wordBytes] at hi; unfold ZoneV; omega) h.v0,
    bytes_keep hk (fun i hi ↦ by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hi; unfold ZoneV; omega) h.high,
    bytes_keep hk (fun i hi ↦ by
      simp only [NativeRustcVm.length_wordBytes] at hi; unfold ZoneV; omega) h.oodN,
    bytes_keep hk (fun i hi ↦ by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hi; unfold ZoneV; omega) h.oodp⟩

theorem FF.keep {m0 : MachineData} {xs ood : Array EW} {v lam : EW} {d d' : Mem 64}
    (h : FF m0 xs ood v lam d) (hk : KeepZ m0 d d') (hx : xs.size ≤ 6) (ho : ood.size ≤ 30) :
    FF m0 xs ood v lam d' :=
  ⟨h.fv.keep hk.v hx ho,
    bytes_keep hk (fun i hi ↦ by
      simp only [NativeRustcVm.length_wordBytes] at hi; unfold Zone; omega) h.l1,
    bytes_keep hk (fun i hi ↦ by
      simp only [NativeRustcVm.length_wordBytes] at hi; unfold Zone; omega) h.l0⟩

section
variable [Labels] {m0 : MachineData}

/-- **A block in `argEnv`** whose writes are in `Gap` ranges keeps `Zone`. -/
theorem keepZ_blk {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    {rs : List (Nat × Nat)} (hW : Wr rs S) (hg : ∀ p ∈ rs, Gap p) : KeepZ m0 d.dmem d'.dmem :=
  fun j hj ↦ hm.get?_mem0 hwf (not_written0A hwf hm hin (by unfold Zone ZoneV at hj; omega)
    fun w hw _ ↦ by
      obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
      have := hg p hp
      unfold Gap at this
      unfold Zone ZoneV at hj
      omega)

/-- **A block in `argEnv`** whose writes are in `GapV` ranges keeps `ZoneV`. -/
theorem keepV_blk {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    {rs : List (Nat × Nat)} (hW : Wr rs S) (hg : ∀ p ∈ rs, GapV p) : KeepV m0 d.dmem d'.dmem :=
  fun j hj ↦ hm.get?_mem0 hwf (not_written0A hwf hm hin (by unfold ZoneV at hj; omega)
    fun w hw _ ↦ by
      obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
      have := hg p hp
      unfold GapV at this
      unfold ZoneV at hj
      omega)

/-- **A block in `frameEnv`** whose writes are in `Gap` ranges keeps `Zone`. -/
theorem keepZ_blkF {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (frameEnv m0 d 8176 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 8176 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    {rs : List (Nat × Nat)} (hW : Wr rs S) (hg : ∀ p ∈ rs, Gap p) : KeepZ m0 d.dmem d'.dmem :=
  fun j hj ↦ hm.get?_mem0 hwf (not_written0 hwf hm hin (by unfold Zone ZoneV at hj; omega)
    fun w hw _ ↦ by
      obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
      have := hg p hp
      unfold Gap at this
      unfold Zone ZoneV at hj
      omega)

end

/-- **A call** from RSP offset `o` changing the frame's `n` bytes from `lo` (a `Gap` range)
keeps `Zone`. -/
theorem keepZ_call {m0 d d' : MachineData} {o lo n : Nat}
    (hk : ∀ j, o + 8 ≤ j → j < 8192 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j))
    (ho : o + 8 ≤ 88) (hg : Gap (lo, lo + n)) : KeepZ m0 d.dmem d'.dmem := fun j hj ↦ by
  unfold Zone ZoneV at hj
  unfold Gap at hg
  exact hk j (by omega) (by omega) (by dsimp only at hg; omega)

theorem two_iff {x y q : BitVec 64} {n m : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩, ⟨y, m⟩] q ↔
      NativeRustcVm.InRange x n q ∨ NativeRustcVm.InRange y m q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]

theorem one_iff {x q : BitVec 64} {n : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩] q ↔ NativeRustcVm.InRange x n q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level w rounds m0)
include c

/-- **Bytes apart from a call's changes** (its stack and `R`) stay. -/
theorem same_call {o : Nat} (ho : o ≤ 8176) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 8176 - o + N' ≤ nextLevelStack) {R : BitVec 64 → Prop}
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q))
    {x : BitVec 64} {mm : Nat} (hxw : x.toNat + mm ≤ 2 ^ 64)
    (hR : ∀ q, R q → ¬NativeRustcVm.InRange x mm q)
    (hs : x.toNat + mm ≤ (rspOf m0).toNat - 11312 ∨ (rspOf m0).toNat + 8 ≤ x.toNat) :
    NativeRustcVm.Layout.Same d.dmem d'.dmem x mm := by
  have g := c.geo
  have hat := c.at_call ho hf
  have hle' : 8176 - o + N' ≤ 11312 := by rw [stack_eq] at hle; exact hle
  have hsb : (stackBelow d N').toNat = (rspOf m0).toNat - 8176 + o - N' := by
    rw [stackBelow_callee hat.sp (by have := g.hN; omega),
      stackBelow_toNat (by have := g.hN; omega)]
    have := g.hN
    omega
  refine NativeRustcVm.Layout.Same.of_sameOutside hch fun j hj hq ↦ ?_
  have hx : (x + BitVec.ofNat 64 j).toNat = x.toNat + j :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rcases hq with hq | hq
  · exact hR _ hq (NativeRustcVm.inRange_add hj (by omega))
  · have := g.hN
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb, hx] at hq
    omega

/-- **A call** from RSP offset `o ≤ 72` changing its stack, the `TState`, the frame's `n` bytes
from `lo ≥ 88` and the query buffer: `K` and the frame's other bytes from `o + 8` kept. -/
theorem K_callO {o : Nat} (ho : o + 8 ≤ 80) {d d' : MachineData}
    (hK : K level w rounds m0 o d) {N' : Nat} (hle : 8176 - o + N' ≤ nextLevelStack)
    (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} {lo n : Nat} (hlo : 88 ≤ lo) (hn : lo + n ≤ 8128)
    (hR : ∀ q, R q → NativeRustcVm.InRange (tA m0) tstateBytes q ∨
      NativeRustcVm.InRange (loc m0 lo) n q ∨ NativeRustcVm.InRange (qA m0) 1848 q)
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q)) :
    K level w rounds m0 (o + 8) d' ∧ ∀ j, o + 8 ≤ j → j < 8192 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j) := by
  have g := c.geo
  have hqa : (qA m0).toNat = (pA m0).toNat + 61352 :=
    NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)
  obtain ⟨hf', hkeep⟩ := c.call (o := o) (by omega) hK.fr hle hsv hrsp (by omega) hn
    (fun q hq ↦ by
      rcases hR q hq with hq | hq | hq
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
      · left; left
        rw [c.inP]
        rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hqa]; have := g.pW; omega), hqa]
          at hq
        omega) hch
  have hsame : ∀ {x : BitVec 64} {mm : Nat}, x.toNat + mm ≤ 2 ^ 64 →
      (x.toNat + mm ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ x.toNat) →
      (x.toNat + mm ≤ (rspOf m0).toNat - 11312 ∨ (rspOf m0).toNat + 8 ≤ x.toNat) →
      (x.toNat + mm ≤ (qA m0).toNat ∨ (qA m0).toNat + 1848 ≤ x.toNat) →
      NativeRustcVm.Layout.Same d.dmem d'.dmem x mm := by
    intro x mm hxw ht hs hq
    refine c.same_call (by omega) hK.fr hle hch hxw (fun q hq' hx ↦ ?_) hs
    have := g.hN
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hx
    rcases hR _ hq' with h' | h' | h'
    · rw [c.inT] at h'; omega
    · rw [c.inLc (by omega) (by omega)] at h'; omega
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hqa]; have := g.pW; omega), hqa] at h'
      rw [hqa] at hq; omega
  have hqa' := hqa
  have hlb : levelBytes = 24 := rfl
  refine ⟨⟨hf', ?_, ?_, ?_⟩, hkeep⟩
  · exact bytes_call hkeep (j := 80) (by omega) (by simp [NativeRustcVm.length_wordBytes])
      (by simp [NativeRustcVm.length_wordBytes]; omega) hK.w80
  · refine LevelAt.of_same hK.lv (hsame g.lW ?_ ?_ ?_)
    · have := g.lT; omega
    · have := g.lS; omega
    · rw [hqa]; have := g.lP; omega
  · refine whirAt_of_same hK.wa (hsame (by have := g.pW; omega) ?_ ?_ ?_)
    · have := g.pT; omega
    · have := g.pS; omega
    · rw [hqa']; omega

/-- A frame range `[j, j + n)` in the frame's first `j + n` bytes. -/
theorem loc_fa {j n : Nat} (hjn : j + n ≤ 8192) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (loc m0 j) n q) : NativeRustcVm.InRange (fa m0) (j + n) q := by
  have := c.geo.hN; have := c.geo.hA
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  rw [c.inLc (by omega) hjn] at hq
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [c.fa_toNat]; omega), c.fa_toNat]
  omega

/-- **A block changing only RCX and the frame's bytes from `lo ≥ 760`** keeps `K` and `Zone`. -/
theorem K_low {o : Nat} {d d' : MachineData} (hK : K level w rounds m0 o d)
    (hr : ∀ r, r ≠ .rcx → reg d' r = reg d r) (hkd : Kept d.dmem d'.dmem) {lo n : Nat}
    (hlo : 760 ≤ lo) (hn : lo + n ≤ 8128)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (loc m0 lo) n)) :
    K level w rounds m0 o d' ∧ KeepZ m0 d.dmem d'.dmem := by
  have g := c.geo
  have hf := hK.fr.frame
  have hnot : ∀ j, j < 8192 → (j < lo ∨ lo + n ≤ j) → ¬NativeRustcVm.InRange (loc m0 lo) n (loc m0 j) :=
    fun j hj hj' hq ↦ by
      have := g.hN
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · exact absurd hq (by unfold NativeRustcVm.InRange; omega)
      rw [c.inLc (by omega) (by omega), c.loc_toNat hj] at hq
      omega
  have hkeep : ∀ j, j < 8192 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j) := fun j hj hj' ↦ hs _ (hnot j hj hj')
  have hfa : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) (lo + n)) :=
    NativeRustcVm.SameOutside.mono hs fun q hq ↦ c.loc_fa (by omega) hq
  have hrcx : calleeSaved .rcx = false := rfl
  refine ⟨⟨⟨⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hkd, fun r hr' hsl ↦ ?_⟩,
    NativeRustcVm.SameOutside.mono (hK.fr.same.trans hs) fun q hq ↦ ?_⟩, ?_,
    LevelAt.of_same hK.lv (c.l_frame (by omega) hfa),
    WhirAt.of_same hK.wa (c.p_frame (by omega) hfa)⟩, fun j hj ↦ ?_⟩
  · show reg d' .rsp = _
    rw [hr .rsp (by decide)]
    exact hf.sp
  · have := slots_ge p hp; have := slots_le p hp
    exact bytes_keep (Z := fun j ↦ j < 8192 ∧ (j < lo ∨ lo + n ≤ j))
      (fun j hj ↦ hkeep j hj.1 hj.2) (fun i hi ↦ by
        simp only [NativeRustcVm.length_wordBytes] at hi; exact ⟨by omega, by omega⟩)
      (hf.slot p hp)
  · exact (hkeep (8176 + j) (by omega) (by omega)).trans (hf.ret j hj)
  · rw [hr r (by rintro rfl; rw [hrcx] at hr'; cases hr')]
    exact hf.regs r hr' hsl
  · rcases hq with hq | hq
    · exact hq
    · left
      obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
      rw [off_add]
      exact c.loc_stk (by omega)
  · exact bytes_keep (Z := fun j ↦ j < 8192 ∧ (j < lo ∨ lo + n ≤ j))
      (fun j hj ↦ hkeep j hj.1 hj.2) (fun i hi ↦ by
        simp only [NativeRustcVm.length_wordBytes] at hi; exact ⟨by omega, by omega⟩) hK.w80
  · unfold Zone ZoneV at hj
    exact hkeep j (by omega) (by omega)

end Ctx

end

end

end NativeRustcVmX64.Whir.Levels.NL
