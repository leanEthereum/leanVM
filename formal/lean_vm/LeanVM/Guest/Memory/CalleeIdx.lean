/-
  LeanVM.Guest.Memory.CalleeIdx

  A callee's index (`calleeIdx`) names it (`calleeIdx_spec`).
-/

module

public import LeanVM.Guest.Memory.GuestCalleesOk
public import LeanVM.Guest.Memory.GuestIdx

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

theorem encL_inj : ∀ {a b : List UInt8}, encL a = encL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [encL] at h; omega
  | _ :: _, [], h => by simp only [encL] at h; omega
  | c :: cs, d :: ds, h => by
      simp only [encL] at h
      have := c.toNat_lt; have := d.toNat_lt
      rw [UInt8.toNat_inj.mp (by omega : c.toNat = d.toNat), encL_inj (by omega : encL cs = encL ds)]

/-- **Names are told apart by their encodings.** -/
theorem encS_inj {s t : String} (h : encS s = encS t) : s = t :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (encL_inj h)))

/-- **A callee's index names it.** -/
theorem calleeIdx_spec {j k : ℕ} {g : String} (h : calleeIdx j g = some k) :
    (coreProgram[k]?).map Fn.name = some g := by
  unfold calleeIdx calleeIdxE at h
  have hm := List.mem_of_find?_eq_some h
  have hn : (Data.encT.find k).any (Nat.beq · (encS g)) = true :=
    List.find?_some (p := fun k ↦ (Data.encT.find k).any (Nat.beq · (encS g))) h
  have hk : k < coreProgram.length := by
    unfold Data.calleesJ at hm
    rcases hf : Data.calleeT.find j with _ | l
    · rw [hf] at hm; simp at hm
    · rw [hf] at hm
      have := NTree.find_all Data.calleeT_lt hf
      have := List.all_eq_true.mp this k hm
      simpa [coreProgram_length] using this
  rcases he : Data.encT.find k with _ | e
  · simp [he] at hn
  · rw [he] at hn
    have hb : e = encS g := Nat.eq_of_beq_eq_true hn
    rw [List.getElem?_eq_getElem hk, Option.map_some, encS_inj ((Data.encT_spec hk he).trans hb)]

end
end LeanVM.Guest.Memory
