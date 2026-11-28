module

public import NativeRustcVmX64.Spec.KeccakGkr
public import NativeRustcVm.Tables.Same
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Update

/-!
# Footprints as numbers (x86-64)

`Areas m n ws rs` as facts on addresses as numbers (`Areas.nat`): every region within the address
space, the written ones and the read ones apart from the stack below RSP with the return address,
the written ones pairwise apart and apart from the read ones (`Sep`). Bytes a change misses stay
(`same_num`), and with them a representation (`TStateAt`, `ClaimsWAt`, elements, words).
-/

namespace NativeRustcVmX64.KeccakGkr

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm (Region)

@[expose] public section

/-- Two ranges of addresses as numbers are apart. -/
def Sep (x n y k : Nat) : Prop := x + n ≤ y ∨ y + k ≤ x

end

public section

theorem sep_of_apart {a b : BitVec 64} {n k : Nat} (h : NativeRustcVm.Apart a n b k) :
    Sep a.toNat n b.toNat k := h

/-- **A footprint as numbers.** -/
theorem Areas.nat [Labels] {m : MachineData} {n : Nat} {ws rs : List Region}
    (h : Areas m n ws rs) :
    (∀ r ∈ ws ++ rs, r.addr.toNat + r.size ≤ 2 ^ 64) ∧
      (∀ w ∈ ws, Sep w.addr.toNat w.size (stackBelow m n).toNat (n + 8)) ∧
      (∀ r ∈ rs, Sep r.addr.toNat r.size (stackBelow m n).toNat (n + 8)) ∧
      ws.Pairwise (fun w w' ↦ Sep w.addr.toNat w.size w'.addr.toNat w'.size) ∧
      (∀ w ∈ ws, ∀ r ∈ rs, Sep w.addr.toNat w.size r.addr.toNat r.size) := by
  obtain ⟨hok, hd, hap⟩ := h
  rw [NativeRustcVm.disjoint_cons_iff] at hd
  refine ⟨fun r hr ↦ (hok r hr).2, fun w hw ↦ ?_, fun r hr ↦ ?_, ?_, fun w hw r hr ↦ ?_⟩
  · have := hd.1 w hw
    unfold NativeRustcVm.Apart at this
    simp only [stackRegion] at this
    unfold Sep; omega
  · have := hap _ List.mem_cons_self r hr
    unfold NativeRustcVm.Apart at this
    simp only [stackRegion] at this
    unfold Sep; omega
  · exact hd.2.imp fun h ↦ h
  · exact hap w (List.mem_cons_of_mem _ hw) r hr

/-- **A footprint from numbers.** -/
theorem areas_of [Labels] {m : MachineData} {n : Nat} {ws rs : List Region}
    (hmap : ∀ r ∈ ws ++ rs, NativeRustcVm.Mapped m.dmem r.addr r.size)
    (hnw : ∀ r ∈ ws ++ rs, r.addr.toNat + r.size ≤ 2 ^ 64)
    (hws : ws.Pairwise (fun w w' ↦ Sep w.addr.toNat w.size w'.addr.toNat w'.size))
    (hwst : ∀ w ∈ ws, Sep w.addr.toNat w.size (stackBelow m n).toNat (n + 8))
    (hrst : ∀ r ∈ rs, Sep (stackBelow m n).toNat (n + 8) r.addr.toNat r.size)
    (hwr : ∀ w ∈ ws, ∀ r ∈ rs, Sep w.addr.toNat w.size r.addr.toNat r.size) :
    Areas m n ws rs := by
  refine ⟨fun r hr ↦ ⟨hmap r hr, hnw r hr⟩, ?_, ?_⟩
  · rw [NativeRustcVm.disjoint_cons_iff]
    refine ⟨fun w hw ↦ ?_, hws.imp fun h ↦ h⟩
    have := hwst w hw
    unfold Sep at this
    show NativeRustcVm.Apart (stackBelow m n) (n + 8) w.addr w.size
    unfold NativeRustcVm.Apart
    omega
  · intro w hw r hr
    rcases List.mem_cons.mp hw with rfl | hw
    · have := hrst r hr
      unfold Sep at this
      show NativeRustcVm.Apart (stackBelow m n) (n + 8) r.addr r.size
      unfold NativeRustcVm.Apart
      omega
    · exact hwr w hw r hr

theorem Areas.mapped [Labels] {m : MachineData} {n : Nat} {ws rs : List Region}
    (h : Areas m n ws rs) {r : Region} (hr : r ∈ ws ∨ r ∈ rs) :
    NativeRustcVm.Mapped m.dmem r.addr r.size :=
  (h.1 r (List.mem_append.mpr hr)).1

/-- **Bytes a change misses** stay. -/
theorem same_num {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    {A : BitVec 64} {k : Nat} (hA : A.toNat + k ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + k ≤ q.toNat) :
    NativeRustcVm.Layout.Same d d' A k := by
  intro j hj
  apply hs
  intro hq
  have := hR _ hq
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
  omega

theorem inR_nat {x q : BitVec 64} {n : Nat} (hnw : x.toNat + n ≤ 2 ^ 64)
    (h : NativeRustcVm.InRange x n q) : x.toNat ≤ q.toNat ∧ q.toNat < x.toNat + n :=
  (NativeRustcVm.inRange_iff hnw).mp h

/-- **The `TState`** stays where a change misses it and its decoded words. -/
theorem ts_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {t : BitVec 64} {a : DecArea} {s : TState}
    (hts : TStateAt d t a s) (hk : Keeps d d') (hs : NativeRustcVm.SameOutside d d' R)
    (htW : t.toNat + 760 ≤ 2 ^ 64) (hwW : a.words.toNat + 8 * a.len ≤ 2 ^ 64)
    (hR : ∀ q, R q → (q.toNat < t.toNat ∨ t.toNat + 760 ≤ q.toNat) ∧
      (q.toNat < a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ q.toNat)) :
    TStateAt d' t a s :=
  have e : tstateBytes = 760 := rfl
  hts.frame hk (fun q hq ↦ ⟨fun ht ↦ by
      have := inR_nat (n := tstateBytes) (by rw [e]; exact htW) ht; have := hR q hq; omega,
    fun ht ↦ by have := inR_nat hwW ht; have := hR q hq; omega⟩) hs

/-- **The column claims** stay where a change misses them. -/
theorem cls_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {c : BitVec 64}
    {cs : Array ColumnClaimW} (hc : NativeRustcVm.Layout.ClaimsWAt d c cs)
    (hs : NativeRustcVm.SameOutside d d' R) (hcW : c.toNat + 97288 ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < c.toNat ∨ c.toNat + 97288 ≤ q.toNat) :
    NativeRustcVm.Layout.ClaimsWAt d' c cs :=
  NativeRustcVm.Tables.ClaimsWAt.of_same hc (same_num hs hcW hR)

/-- **Elements** stay where a change misses them. -/
theorem ews_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {A : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.EWsAt d A xs) (hs : NativeRustcVm.SameOutside d d' R)
    (hA : A.toNat + 16 * xs.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + 16 * xs.length ≤ q.toNat) :
    NativeRustcVm.EWsAt d' A xs :=
  NativeRustcVm.Tables.EWsAt.of_same h (same_num hs hA hR) le_rfl

/-- **Bytes** stay where a change misses them. -/
theorem bytes_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {A : BitVec 64} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d A bs) (hs : NativeRustcVm.SameOutside d d' R)
    (hA : A.toNat + bs.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + bs.length ≤ q.toNat) :
    NativeRustcVm.BytesAt d' A bs :=
  NativeRustcVm.Layout.BytesAt.of_same h (same_num hs hA hR) le_rfl

/-- **A word** stays where a change misses it. -/
theorem word_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {A : BitVec 64} {w : UInt64}
    (h : NativeRustcVm.WordAt d A w) (hs : NativeRustcVm.SameOutside d d' R)
    (hA : A.toNat + 8 ≤ 2 ^ 64) (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + 8 ≤ q.toNat) :
    NativeRustcVm.WordAt d' A w :=
  NativeRustcVm.Layout.WordAt.of_same h (same_num hs hA hR) le_rfl

/-- **A `Buf<EW, N>`** stays where a change misses it. -/
theorem buf_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {A : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d A N xs) (hs : NativeRustcVm.SameOutside d d' R)
    (hA : A.toNat + 8 + 16 * N ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + 8 + 16 * N ≤ q.toNat) :
    NativeRustcVm.BufEWAt d' A N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, word_keep hw hs (by omega) fun q hq ↦ by have := hR q hq; omega, ?_⟩
  cases xs with
  | nil => exact NativeRustcVm.ewsAt_nil _ _
  | cons x xs' =>
  have hl' : 1 ≤ N := by simp at hl; omega
  have h8 : (A + 8#64).toNat = A.toNat + 8 :=
    NativeRustcVm.toNat_add_ofNat (a := A) (i := 8) (by omega)
  exact ews_keep he hs (by rw [h8]; omega) fun q hq ↦ by
    have := hR q hq
    rw [h8]
    have : 16 * (x :: xs').length ≤ 16 * N := Nat.mul_le_mul_left _ hl
    omega

end

end NativeRustcVmX64.KeccakGkr
