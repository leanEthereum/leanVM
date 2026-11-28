module

public import NativeRustcVmArm.Bus.AccumulateSide.Loop5
public import NativeRustcVmArm.Basic

/-!
# `accumulate_side`: the owner's padding row in read-only data
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- The span selected from `TABLES` is a readable padding row, disjoint from the callee's stack. -/
theorem padding_slice [Labels] {m : MachineData} {s o : Nat} (hr : RodataAt m s) (ho : o < 6)
    {p n : UInt64}
    (hp : p.toBitVec = NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 *
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toNat))
    (hn : n.toNat = (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 4) 0).toNat) :
    SliceOk m p n s ∧ slice m p n = (tablesW.getD o default).padding := by
  let start := (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toNat
  let len := (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 4) 0).toNat
  obtain ⟨hbound, hdata⟩ := padding_read ho
  change start + len < 154 at hbound
  have hpositive : ∀ o : Fin 6, 0 <
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o.val + 4) 0).toNat := by decide +kernel
  have hpos : 0 < len := hpositive ⟨o, ho⟩
  change (NativeRustcVm.Data.padding.drop start).take len = (tablesW.getD o default).padding.toList at hdata
  have hlen : len = (tablesW.getD o default).padding.size := by
    have hlen := congrArg List.length hdata
    simp only [List.length_take, List.length_drop, padding_length, Array.length_toList] at hlen
    omega
  have bytes : NativeRustcVm.Data.Item.padding.bytes.length = 2448 := by decide +kernel
  have hpad : NativeRustcVm.EWsAt m.dmem (NativeRustcVmArm.rodataAddr .padding)
      NativeRustcVm.Data.padding := (hr .padding).1
  have hw := (hpad.drop start).take len
  rw [hdata] at hw
  have hsize := (hr .padding).2.1
  rw [bytes] at hsize
  change (NativeRustcVmArm.rodataAddr .padding).toNat + 2448 ≤ 2 ^ 64 at hsize
  have haddr : (NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 * start)).toNat =
      (NativeRustcVmArm.rodataAddr .padding).toNat + 16 * start :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  constructor
  · unfold SliceOk
    rw [hp, hn]
    change Readable m (NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 * start)) (16 * len) ∧
      OffStack m (NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 * start)) (16 * len) s
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mapped_eq]
      simpa only [Array.length_toList, ← hlen] using hw.mapped
    · unfold NoWrap
      rw [haddr]
      omega
    · have hap := (hr .padding).2.2
      rw [bytes] at hap
      unfold OffStack Apart
      unfold NativeRustcVm.Apart at hap
      rw [haddr]
      omega
  · unfold slice
    rw [hp, hn]
    change (NativeRustcVm.ewsOf m.dmem
      (NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 * start)) len).toArray = _
    rw [hlen, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hw]

private theorem lowBit_mod64 (n k : Nat) (hk : k < 64) :
    ((n % 2 ^ 64) >>> k) % 2 = (n >>> k) % 2 := by
  have hd : 2 ^ k * 2 ∣ 2 ^ 64 := by
    rw [← Nat.pow_succ]
    exact Nat.pow_dvd_pow 2 (by omega)
  simp only [Nat.shiftRight_eq_div_pow]
  rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd n hd, Nat.mod_mul_right_div_self]

/-- `paddingWeight` reads only the low 64 bits when the point has fewer than 64 coordinates. -/
theorem paddingWeight_mod64 (point : Array EW) (n : Nat) (hp : point.size < 64) :
    paddingWeight point (n % 2 ^ 64) = paddingWeight point n := by
  have fold_eq (xs : List (EW × Nat)) (hx : ∀ x ∈ xs, x.2 < 64) (acc : EW) :
      xs.foldl (fun pad (r, k) ↦
        let b := EW.ofNat (((n % 2 ^ 64) >>> k) % 2)
        (1 + b) * r + (1 + b + r) * pad) acc =
      xs.foldl (fun pad (r, k) ↦
        let b := EW.ofNat ((n >>> k) % 2)
        (1 + b) * r + (1 + b + r) * pad) acc := by
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨r, k⟩
      simp only [List.foldl_cons]
      rw [lowBit_mod64 n k (hx (r, k) (List.mem_cons_self))]
      exact ih (fun x hx' ↦ hx x (List.mem_cons_of_mem _ hx')) _
  unfold paddingWeight
  rw [lowBit_mod64 n point.size hp]
  congr 1
  simp only [← Array.foldl_toList]
  apply fold_eq
  intro x hx
  have hm : x ∈ point.zipIdx := Array.mem_toList_iff.mp hx
  have hb := Array.mem_zipIdx hm
  omega

end

end NativeRustcVmArm.Bus.AccumulateSide
