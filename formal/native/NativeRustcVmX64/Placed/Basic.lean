module

public import NativeRustcX64.Basic

/-!
# Placement from distinct labels

A program whose labels are pairwise distinct (`(labels P).Nodup`, one kernel check over the
program) has each label at its only `.label` directive (`findIdx?_of_nodup`), so a function's code
at a known index is `Placed` (`placed_of_nodup`) with no per-label check.
-/

namespace NativeRustcVmX64.Placement

open NativeRustcX64

@[expose] public section

/-- The label a directive defines. -/
def labelOf : Directive → Option Label
  | .label l => some l
  | _ => none

/-- The labels a program defines, in order. -/
def labels (P : List Directive) : List Label := P.filterMap labelOf

/-- A byte string as a number, injectively: base 257, digits `b + 1`. -/
def enc : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 1 + 257 * enc bs

/-- A label as a number, injectively (`key_inj`): the kernel compares numbers fast, strings
slowly. -/
def key (s : Label) : Nat := enc s.toByteArray.data.toList

end

public section

theorem enc_inj : ∀ {l l' : List UInt8}, enc l = enc l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [enc] at h; omega
  | _ :: _, [], h => by simp only [enc] at h; omega
  | b :: bs, b' :: bs', h => by
    simp only [enc] at h
    have hb := b.toNat_lt
    have hb' := b'.toNat_lt
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : enc bs = enc bs' := by omega
    rw [UInt8.toNat_inj.mp h1, enc_inj h2]

theorem key_inj {s t : Label} (h : key s = key t) : s = t := by
  have hd : s.toByteArray.data = t.toByteArray.data := Array.toList_inj.mp (enc_inj h)
  apply String.toByteArray_inj.mp
  calc s.toByteArray = ⟨s.toByteArray.data⟩ := rfl
    _ = ⟨t.toByteArray.data⟩ := by rw [hd]
    _ = t.toByteArray := rfl

/-- Labels whose numbers are distinct are distinct. -/
theorem nodup_of_keys {P : List Directive} (h : ((labels P).map key).Nodup) : (labels P).Nodup :=
  List.Pairwise.of_map key (fun _ _ hk he ↦ hk (congrArg key he)) h

/-- In a program with distinct labels, a label's directive is the first of its name. -/
theorem findIdx?_of_nodup {P : List Directive} (h : (labels P).Nodup) {i : Nat} {l : Label}
    (hi : P[i]? = some (.label l)) : P.findIdx? (· = .label l) = some i := by
  obtain ⟨hil, hPi⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hil, by simp [hPi], fun j hj hPj ↦ ?_⟩
  simp only [decide_eq_true_eq] at hPj
  rw [labels, ← List.take_append_drop i P, List.filterMap_append, List.nodup_append] at h
  have h1 : l ∈ (P.take i).filterMap labelOf :=
    List.mem_filterMap.mpr ⟨P[j], List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩,
      by simp [hPj, labelOf]⟩
  have h2 : l ∈ (P.drop i).filterMap labelOf :=
    List.mem_filterMap.mpr ⟨P[i], List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩,
      by simp [hPi, labelOf]⟩
  exact h.2.2 l h1 l h2 rfl

/-- **A function placed** in a program with distinct labels: its code at index `k`. -/
theorem placed_of_nodup [Host] {P : List Directive} (hP : Host.prog = P)
    (hn : (labels P).Nodup) {F : List Directive} {k : Nat} (hF : F.IsInfixAt P k) :
    Placed F k := by
  refine ⟨hP ▸ hF, fun j h ↦ ?_⟩
  have hj := List.isInfixAt_iff_getElem?.mp hF j h
  generalize F[j] = d at hj ⊢
  cases d with
  | label l =>
    show Host.prog.findIdx? (· = .label l) = some (k + j)
    rw [hP]
    exact findIdx?_of_nodup hn hj
  | _ => trivial

end

end NativeRustcVmX64.Placement
