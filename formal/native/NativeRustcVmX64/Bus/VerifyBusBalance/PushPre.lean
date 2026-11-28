module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Pull

/-!
# `verify_bus_balance`'s push side: what it starts from (x86-64)

- `PushMem`: the frame's locals at `b43` (the three layouts, the weights, the GKR state, the
  point, the memory's scalars, the final counters, the β, the share); `PushMem.of_keep`.
- `mask_toNat`: `!(-1 << x)` is `2^x - 1`.
- `forms0_at`, `fits_forms0`: the emptied forms.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- **The locals at `b43`.** -/
structure PushMem (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW)
    (beta mf bf share : EW) (d : Mem 64) : Prop where
  tail : TailMem m0 pt d
  push : BusLayoutWAt d (loc m0 2808) (pushL L)
  pull : BusLayoutWAt d (loc m0 3696) (pullL L)
  count : BusLayoutWAt d (loc m0 4584) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 368) w.toList
  wsz : w.size = 16
  hmem : NativeRustcVm.EWsAt d (loc m0 216) mem.toList
  msz : mem.size = 2
  htv : NativeRustcVm.EWsAt d (loc m0 1744) tv.toList
  tsz : tv.size = 3
  w168 : NativeRustcVm.WordAt d (loc m0 168) mf.c0
  w160 : NativeRustcVm.WordAt d (loc m0 160) mf.c1
  w152 : NativeRustcVm.WordAt d (loc m0 152) bf.c0
  w144 : NativeRustcVm.WordAt d (loc m0 144) bf.c1
  w184 : NativeRustcVm.WordAt d (loc m0 184) beta.c0
  w176 : NativeRustcVm.WordAt d (loc m0 176) beta.c1
  share : NativeRustcVm.EWAt d (loc m0 352) share

/-- The locals' intervals at `b43`. -/
abbrev pushIv : List (Nat × Nat) := [(104, 128), (144, 192), (216, 248), (352, 624), (1744, 5472)]

theorem PushMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf share : EW} {d d' : Mem 64} (h : PushMem m0 L w pt tv mem beta mf bf share d)
    (hk : KeepIv pushIv m0 d d') : PushMem m0 L w pt tv mem beta mf bf share d' := by
  have psz := h.tail.psz
  have i1 : (104, 128) ∈ pushIv := by simp
  have i2 : (144, 192) ∈ pushIv := by simp
  have i3 : (216, 248) ∈ pushIv := by simp
  have i4 : (352, 624) ∈ pushIv := by simp
  have i5 : (1744, 5472) ∈ pushIv := by simp
  have w2 : ∀ {o : Nat} {x : UInt64}, 144 ≤ o → o + 8 ≤ 192 →
      NativeRustcVm.WordAt d (loc m0 o) x → NativeRustcVm.WordAt d' (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn i2 h1 h2) le_rfl
  have hk4 : KeepIv tailIv m0 d d' := fun j ⟨p, hp, h1, h2⟩ ↦ hk j (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨_, i1, by simp only at h1 h2 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩
    · exact ⟨_, i5, by simp only at h1 h2 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩)
  have hb : busLayoutBytes = 888 := busLayoutBytes_eq
  refine ⟨h.tail.of_keep hk4,
    BusLayoutWAt.of_same h.push (hk.sameIn i5 (by omega) (by omega)),
    BusLayoutWAt.of_same h.pull (hk.sameIn i5 (by omega) (by omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i5 (by omega) (by omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i4 (n := 256) (by omega) (by omega))
      (by rw [Array.length_toList, h.wsz]), h.wsz,
    NativeRustcVm.Tables.EWsAt.of_same h.hmem (hk.sameIn i3 (n := 32) (by omega) (by omega))
      (by rw [Array.length_toList, h.msz]), h.msz,
    NativeRustcVm.Tables.EWsAt.of_same h.htv (hk.sameIn i5 (n := 48) (by omega) (by omega))
      (by rw [Array.length_toList, h.tsz]), h.tsz,
    w2 (by omega) (by omega) h.w168, w2 (by omega) (by omega) h.w160,
    w2 (by omega) (by omega) h.w152, w2 (by omega) (by omega) h.w144,
    w2 (by omega) (by omega) h.w184, w2 (by omega) (by omega) h.w176,
    NativeRustcVm.Layout.EWAt.of_same h.share (hk.sameIn i4 (n := 16) (by omega) (by omega))
      le_rfl⟩

/-- **`!(-1 << x)`** is `2^x - 1`, `x` below `64`. -/
theorem mask_toNat {x : BitVec 64} (hx : x.toNat < 64) :
    (UnOp.apply .not .W64 (BinOp.apply .shl .W64 (BitVec.ofNat 64 18446744073709551615)
      (UnOp.apply .trunc .W32 x))).toNat = 2 ^ x.toNat - 1 := by
  have hs : shiftCount .W64 (ext .W32 (low .W32 x)) = x.toNat := by
    simp only [shiftCount, low, ext, shiftMask, BitVec.toNat_setWidth]
    rw [show (0x3f : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [Width.bits]
    omega
  simp only [UnOp.apply, BinOp.apply, low_W64, ext_W64]
  rw [hs, BitVec.toNat_not, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have h1 := Nat.one_le_two_pow (n := x.toNat)
  have h2 : 2 ^ x.toNat ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨c, hc⟩ := h2
  generalize 2 ^ x.toNat = P at h1 hc ⊢
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at hc ⊢
  have hc1 : 1 ≤ c := by rcases c with _ | c <;> simp_all
  have e : 18446744073709551615 % 18446744073709551616 * P =
      18446744073709551616 * (P - 1) + (18446744073709551616 - P) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    have : P ≤ 18446744073709551616 := by rw [hc]; exact Nat.le_mul_of_pos_right _ hc1
    rw [Nat.mul_sub, Nat.mul_one]
    have : 18446744073709551616 ≤ 18446744073709551616 * P := Nat.le_mul_of_pos_right _ h1
    omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `tablesW` has a table per table. -/
theorem tablesW_size' : tablesW.size = nTables := by simp [tablesW]; rfl

/-- The emptied forms' slots. -/
theorem slot_forms0 (t side : Nat) : (forms0.getD t #[]).getD side #[] = #[] := by
  simp only [forms0, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases tablesW[t]? with
  | none => rfl
  | some _ => rcases side with _ | _ | _ | side <;> rfl

/-- **The emptied forms**: a count `0` at each form's first word. -/
theorem forms0_at {d : Mem 64} {a : BitVec 64}
    (h : ∀ j < 18, NativeRustcVm.WordAt d (off a (5928 * j)) 0) : FormsAt d a forms0 := by
  have hs : forms0.size = nTables := by simp [forms0, tablesW_size']
  have hrow : ∀ t (ht : t < forms0.size), forms0[t] = #[#[], #[], #[]] := fun t ht ↦ by
    simp [forms0]
  refine ⟨hs, fun t ht ↦ by rw [hrow t ht]; rfl, fun t ht s hs' ↦ ?_⟩
  have h3 : s < 3 := by rw [hrow t ht] at hs'; simpa using hs'
  have hf : forms0[t][s] = #[] := by
    have e := slot_forms0 t s
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht,
      Option.getD_some, Array.getElem?_eq_getElem hs', Option.getD_some] at e
    exact e
  rw [hf]
  have ht' : t < 6 := by rw [hs] at ht; exact ht
  exact ⟨by simp, h (3 * t + s) (by omega), fun i h' ↦ absurd h' (by simp)⟩

/-- **The emptied forms fit** before side `0`. -/
theorem fits_forms0 : FitsUpTo forms0 0 := by
  refine ⟨⟨by simp [forms0, tablesW_size'], fun row hr ↦ ?_⟩, fun o _ s _ ↦
    ⟨fun h ↦ absurd h (by omega), fun _ ↦ ?_⟩⟩
  · simp only [forms0, Array.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    rfl
  · unfold slot
    rw [slot_forms0]
    rfl

end

end NativeRustcVmX64.Bus.VerifyBusBalance
