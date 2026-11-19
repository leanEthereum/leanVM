module

public import X86.Keccak.Tail

/-!
# `Keccak.hash`'s proof: the whole run

Zero the lanes, absorb the whole blocks (`absorb_spec`), XOR in the remaining words
(`tail_spec`), pad (`pad_spec`) and permute: the lanes end as `keccak256`'s final state
(`hash_correct`, which `X86.Keccak.Spec` states as `hash_spec`).
-/

@[expose] public section

namespace X86.Keccak.Proof

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

theorem hash_eq : hash = blk (
    blk ((List.range 25).map fun k ↦ I (.storei (atDi (sA + 8 * k.toInt64)) 0)) ::
    absorbLoop :: I (.movi .rcx 0) :: tailLoop :: ((padP1 ++ padP2) ++ [permute])) := (rfl)

/-- **`Keccak.hash` is Keccak-256.** -/
theorem hash_correct {s : QState} {ws : List UInt64} {len : Nat} {E : QState → Prop}
    (hb : HoldsBytes ws len) (hlen : s.reg .rbx = len.toUInt64) (hlen32 : len < 2 ^ 32)
    (hin : WordsAt s.mem (s.reg .rsi) ws)
    (hscr : ∀ k < scratchWords, (s.mem (scratchAddr (s.reg .rdi) k)).isSome)
    (hdisj : ∀ i < ws.length, ∀ k < scratchWords,
      s.reg .rsi + (8 * i).toUInt64 ≠ scratchAddr (s.reg .rdi) k) :
    WP hash s (fun s' ↦
      (∀ k (hk : k < 4), s'.mem (scratchAddr (s.reg .rdi) k) =
        some (keccak256 ((wordsBytes ws).take len))[k]) ∧
      (∀ k < scratchWords, (s'.mem (scratchAddr (s.reg .rdi) k)).isSome) ∧
      (∀ a, (∀ k < scratchWords, a ≠ scratchAddr (s.reg .rdi) k) → s'.mem a = s.mem a) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  rw [hash_eq]
  apply WP.blk_cons
  refine WP.mono (zero_spec rfl hscr) ?_ (fun _ h ↦ h)
  rintro s1 ⟨hok1, hR1, hF1, hZ1⟩
  have hrun1 : Run s s1 := ⟨hok1, RegsFrame.mono hR1 (by simp), hF1.widen le_rfl (by omega)⟩
  apply WP.blk_cons
  refine WP.mono (absorb_spec hb hlen32 hin hdisj
    ⟨0, Vector.replicate 25 0, by omega, ?_, ?_, hrun1, ?_, ?_⟩) ?_ (fun _ h ↦ h)
  · rw [hR1 _ (by simp)]
    simp
  · rw [hR1 _ (by simp), hlen]
    simp
  · exact hZ1.congr fun t ht ↦ (lane_replicate ht).symm
  · simp
  rintro s2 ⟨⟨j, A, hj, hrsi2, hrbx2, hrun2, hA2, hab2⟩, hlt⟩
  have hjN : j = len / 136 := by
    rw [hrbx2, toNat_toUInt64 (by omega)] at hlt
    omega
  subst hjN
  refine wp_op rfl ?_
  apply WP.blk_cons
  refine WP.mono (tail_spec (A := A) hb hin hdisj
    ⟨0, by omega, ?_, ?_, ?_, hrun2.setReg (by simp) _, ?_⟩) ?_ (fun _ h ↦ h)
  · simp only [QState.setReg_reg, ↓reduceIte]
    rfl
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrsi2]
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrbx2]
    congr 1
    omega
  · intro i hi
    simp only [QState.setReg_mem, tailLanes, Nat.not_lt_zero, ↓reduceIte]
    exact hA2 i hi
  rintro s3 ⟨hrbx3, hrun3, hW3⟩
  refine wp_blk_append (WP.mono (pad_spec (Nat.mod_lt _ (by omega)) hrun3.rdi hrbx3 hrun3.ok hW3)
    ?_ (fun _ h ↦ h))
  rintro s4 ⟨hok4, hR4, hF4, hW4⟩
  have hrun4 : Run s s4 := hrun3.next hR4 (by simp) hF4 hok4
  have hX : Words s4.mem (s.reg .rdi) 0 25 (Keccak.lane (xorRate A (littleEndianLane
      (padBlock (((wordsBytes ws).take len).drop (136 * (len / 136))))))) :=
    hW4.congr fun i hi ↦ (lane_lastBlock hb A hi).symm
  apply WP.blk_cons
  refine WP.mono (permute_spec hrun4.rdi hrun4.ok hX) ?_ (fun _ h ↦ h)
  rintro s5 ⟨hok5, hR5, hF5, hA5⟩
  have hrun5 : Run s s5 := hrun4.next hR5 (by simp) hF5 hok5
  refine WP.blk_nil ⟨fun k hk ↦ ?_, hrun5.ok, fun a ha ↦ hrun5.frame a fun k _ hk ↦ ha k hk,
    hrun5.regs⟩
  rw [keccak256_lane _ hk, length_held hb, ← hab2, Nat.sub_self, absorbWith_zero]
  have := hA5 k (by omega)
  rwa [Nat.zero_add] at this

end X86.Keccak.Proof
