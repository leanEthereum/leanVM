module

public import NativeRustcArm.Sym
public import NativeRustcVm.Whir.Rep
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.MemLemmas

/-!
# The state's bytes across `glue_level`'s steps

`glue_level` writes the state at `p` piecewise: the claim, the glued claims' count, the two new
glued claims' fields and buffers. Between two points of the run memory agrees with the earlier one
on the state's bytes but at the offsets `W` written (`Agree d d' p N W`): from a block's run
(`agree_of_foot`, its writes placed by `Foot`) or a callee's changed range (`agree_of_inRange`).
A representation over bytes no later step writes is kept (`bytesAt_of_agree`, `bufEWAt_of_agree`,
`bufWordsAt_of_agree`, `gluedAt_of_agree`, each from `agree_sub` of the area's agreement).
-/

namespace NativeRustcVmArm.Whir

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm (WordAt EWAt EWsAt WordsAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off Agree)
open NativeRustcVm.Whir (GluedAt GluedWeightAt gluedBytes stackCap queryCap)

public section

variable {d d' : Mem 64}

/-! ## Representations kept -/

/-- Part of an agreement: the `k` bytes at `o`, none written. -/
theorem agree_sub {a : BitVec 64} {n o k : Nat} {W : Nat → Prop} (h : Agree d d' a n W)
    (hle : o + k ≤ n) (hW : ∀ i < k, ¬ W (o + i)) : Agree d d' (off a o) k (fun _ ↦ False) :=
  fun j hj _ ↦ by rw [off_off]; exact h (o + j) (by omega) (hW j hj)

theorem bytesAt_of_agree {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : bs.length ≤ n) (hb : NativeRustcVm.BytesAt d a bs) :
    NativeRustcVm.BytesAt d' a bs :=
  fun i hi ↦ (h i (by omega) id).trans (hb i hi)

theorem wordAt_of_agree {a : BitVec 64} {n : Nat} {w : UInt64}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 8 ≤ n) (hb : WordAt d a w) : WordAt d' a w :=
  bytesAt_of_agree (bs := NativeRustcVm.wordBytes w) h
    (by rw [NativeRustcVm.length_wordBytes]; exact hle) hb

theorem ewAt_of_agree {a : BitVec 64} {n : Nat} {x : EW}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 16 ≤ n) (hb : EWAt d a x) : EWAt d' a x :=
  bytesAt_of_agree (bs := NativeRustcVm.ewBytes x) h
    (by rw [NativeRustcVm.length_ewBytes]; exact hle) hb

theorem bufEWAt_of_agree {a : BitVec 64} {n N : Nat} {xs : List EW}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 8 + 16 * N ≤ n) (hb : BufEWAt d a N xs) :
    BufEWAt d' a N xs := by
  obtain ⟨hl, hw, he⟩ := hb
  refine ⟨hl, wordAt_of_agree h (by omega) hw, ?_⟩
  have h8 : Agree d d' (off a 8) (16 * N) (fun _ ↦ False) := agree_sub h (by omega) fun _ _ ↦ id
  exact bytesAt_of_agree (bs := xs.flatMap NativeRustcVm.ewBytes) h8
    (by rw [NativeRustcVm.length_ewsBytes]; omega) he

theorem bufWordsAt_of_agree {a : BitVec 64} {n N : Nat} {xs : List UInt64}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 8 + 8 * N ≤ n) (hb : BufWordsAt d a N xs) :
    BufWordsAt d' a N xs := by
  obtain ⟨hl, hw, he⟩ := hb
  refine ⟨hl, wordAt_of_agree h (by omega) hw, ?_⟩
  have h8 : Agree d d' (off a 8) (8 * N) (fun _ ↦ False) := agree_sub h (by omega) fun _ _ ↦ id
  exact bytesAt_of_agree (bs := xs.flatMap NativeRustcVm.wordBytes) h8
    (by rw [NativeRustcVm.length_wordsBytes]; omega) he

/-- **A glued claim kept**: its `6064` bytes not written. -/
theorem gluedAt_of_agree {q : BitVec 64} {g : GluedClaimW}
    (h : Agree d d' q gluedBytes (fun _ ↦ False)) (hg : GluedAt d q g) : GluedAt d' q g := by
  have hs : ∀ o k, o + k ≤ gluedBytes → Agree d d' (off q o) k (fun _ ↦ False) :=
    fun o k hle ↦ agree_sub h hle fun _ _ ↦ id
  obtain ⟨sc, fs, w⟩ := g
  obtain ⟨hsc, hfs, h16, hw⟩ := hg
  refine ⟨ewAt_of_agree h (by decide) hsc, hfs, wordAt_of_agree (hs 16 8 (by decide)) le_rfl h16, ?_⟩
  cases w with
  | eq z =>
    obtain ⟨h24, hp⟩ := hw
    exact ⟨wordAt_of_agree (hs 24 8 (by decide)) le_rfl h24,
      bufEWAt_of_agree (hs 40 488 (by decide)) (by decide) hp⟩
  | induced mu qs ws =>
    obtain ⟨h24, hmu, h32, hq, hws⟩ := hw
    exact ⟨wordAt_of_agree (hs 24 8 (by decide)) le_rfl h24, hmu,
      wordAt_of_agree (hs 32 8 (by decide)) le_rfl h32,
      bufWordsAt_of_agree (hs 528 1848 (by decide)) (by decide) hq,
      bufEWAt_of_agree (hs 2376 3688 (by decide)) (by decide) hws⟩

/-! ## Agreements -/

/-- Agreement across two steps. -/
theorem agree_trans {d₁ d₂ : Mem 64} {a : BitVec 64} {n : Nat} {W₁ W₂ : Nat → Prop}
    (h₁ : Agree d d₁ a n W₁) (h₂ : Agree d₁ d₂ a n W₂) : Agree d d₂ a n (fun j ↦ W₁ j ∨ W₂ j) :=
  fun j hj hW ↦ (h₂ j hj fun h ↦ hW (.inr h)).trans (h₁ j hj fun h ↦ hW (.inl h))

theorem agree_mono {a : BitVec 64} {n : Nat} {W W' : Nat → Prop} (h : Agree d d' a n W)
    (hW : ∀ j, W j → W' j) : Agree d d' a n W' :=
  fun j hj hW' ↦ h j hj fun h ↦ hW' (hW j h)

/-- **A callee's change**: memory changed only in `R`, which the bytes of `p` outside `W` avoid. -/
theorem agree_of_sameOutside {p : BitVec 64} {N : Nat} {W : Nat → Prop} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hR : ∀ j < N, ¬ W j → ¬ R (off p j)) : Agree d d' p N W :=
  fun j hj hW ↦ hs _ (hR j hj hW)

/-- An address of `p`'s `N` bytes out of a range `[o, o + n)` of them is outside it, and out of
any range apart from them. -/
theorem not_inRange_off {p : BitVec 64} {N o n j : Nat} (hN : NoWrap p N) (hj : j < N)
    (hle : o + n ≤ N) (hout : j < o ∨ o + n ≤ j) : ¬ InRange (off p o) n (off p j) := by
  unfold NoWrap at hN
  intro h
  have := (NativeRustcVm.Transcript.inRange_off_iff (b := p) (o := o) (n := n) (j := j)
    (by omega) (by omega)).mp h
  omega

theorem not_inRange_apart {p a : BitVec 64} {N n j : Nat} (hN : NoWrap p N) (hn : NoWrap a n)
    (hA : Apart p N a n) (hj : j < N) : ¬ InRange a n (off p j) := by
  unfold NoWrap at hN
  exact NativeRustcVm.Transcript.not_inRange_of_apart hA hN hn
    (NativeRustcVm.Transcript.inRange_off_self hj (by omega))

/-- **Where a block wrote**: each write of `S` in a region at offset `o` of `p`'s `N` bytes, its
bytes there among the offsets `W`. -/
def Foot (env : Env) (S : SState) (p : BitVec 64) (N : Nat) (W : Nat → Prop) : Prop :=
  ∀ w ∈ S.mem, ∀ b sz, env.regions[w.r]? = some (b, sz) →
    ∃ o, b.toNat = p.toNat + o ∧ o + w.off + w.n ≤ N ∧
      ∀ j, o + w.off ≤ j → j < o + w.off + w.n → W j

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- A register a block left: its symbolic value. -/
theorem rv (hm : Match env S m) {r : XReg} {v : Sym} (h : S.reg r = some v) :
    m.regs.getXReg r = UInt64.ofBitVec (v.eval env) :=
  UInt64.toBitVec_inj.mp (hm.regs r v h)

/-- **A block's writes** agree with its start's memory on the bytes of `p` it does not write. -/
theorem agree_of_foot (hm : Match env S m) (hwf : env.WF) {p : BitVec 64} {N : Nat}
    (hN : NoWrap p N) {W : Nat → Prop} (hf : Foot env S p N W) : Agree env.mem0 m.dmem p N W := by
  intro j hj hWj
  refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hWj ?_
  obtain ⟨o, hbo, -, hW⟩ := hf w hw b sz hb
  unfold NoWrap at hN
  rw [toNat_off (by omega)] at h1 h2
  exact hW j (by omega) (by omega)

omit [Labels] in
/-- **Writes in two regions** of `p`'s bytes, at offsets `o₀`, `o₁` of it, each between `lo` and
`hi` in its region (checked on the literal state). -/
theorem foot_two {p : BitVec 64} {N : Nat} {W : Nat → Prop} {r₀ r₁ : Nat} {b₀ b₁ : BitVec 64}
    {sz₀ sz₁ o₀ o₁ lo₀ hi₀ lo₁ hi₁ : Nat} (h₀ : env.regions[r₀]? = some (b₀, sz₀))
    (h₁ : env.regions[r₁]? = some (b₁, sz₁)) (e₀ : b₀.toNat = p.toNat + o₀)
    (e₁ : b₁.toNat = p.toNat + o₁)
    (hS : S.mem.all (fun w ↦ (w.r == r₀ && decide (lo₀ ≤ w.off) && decide (w.off + w.n ≤ hi₀)) ||
      (w.r == r₁ && decide (lo₁ ≤ w.off) && decide (w.off + w.n ≤ hi₁))) = true)
    (hN₀ : o₀ + hi₀ ≤ N) (hN₁ : o₁ + hi₁ ≤ N)
    (hW : ∀ j, (o₀ + lo₀ ≤ j ∧ j < o₀ + hi₀) ∨ (o₁ + lo₁ ≤ j ∧ j < o₁ + hi₁) → W j) :
    Foot env S p N W := by
  intro w hw b sz hb
  have := List.all_eq_true.mp hS w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨⟨hr, hlo⟩, hhi⟩ | ⟨⟨hr, hlo⟩, hhi⟩
  · rw [hr, h₀] at hb
    cases hb
    exact ⟨o₀, e₀, by omega, fun j h1 h2 ↦ hW j (.inl ⟨by omega, by omega⟩)⟩
  · rw [hr, h₁] at hb
    cases hb
    exact ⟨o₁, e₁, by omega, fun j h1 h2 ↦ hW j (.inr ⟨by omega, by omega⟩)⟩

omit [Labels] in
/-- **A block's writes** are among `p`'s bytes. -/
theorem written_of_foot {p : BitVec 64} {N : Nat} (hN : NoWrap p N)
    {W : Nat → Prop} (hf : Foot env S p N W) {q : BitVec 64} (hq : Written env S q) :
    InRange p N q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  obtain ⟨o, hbo, hle, -⟩ := hf w hw b sz hb
  exact (NativeRustcVm.Transcript.inRange_iff' hN).mpr ⟨by omega, by omega⟩

end

end NativeRustcVmArm.Whir
