/-
  LeanVM.Guest.Count.VsBoundBase

  `open_stacked`'s bound per arm with its name spelled by `natStr` (`osC`), so that the kernel
  evaluates it (`openNames` spells the names by `toString`, whose body the kernel cannot see), and
  by the search tree's lookups (`osCF`); `osC m = osCF m` (`osC_eq_fast`), and `osBosAt` at the
  deployed frame sizes is `osC` (`osBosAt_eq`).
-/

module

public import LeanVM.Guest.Count.VsOsDefs
public import LeanVM.Guest.B1.Whir.Names
import LeanVM.Guest.B1.Whir.RateFree

namespace LeanVM.Guest.Count

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

/-- `open_stacked`'s words at the arm `m`, the largest over the rates, its name spelled by `natStr`. -/
noncomputable def osC (m : ℕ) : ℕ :=
  ((List.range ligNRates).map fun ri ↦ B1.osBos B2C.fs wSBos ("open_stacked__L" ++ natStr m) (osCfgR m ri)).foldl
    max 0

theorem foldl_max_map_add {α : Type} (f : α → ℕ) (a b : ℕ) :
    ∀ (l : List α) (acc : ℕ), (l.map fun x ↦ a + f x + b).foldl max (a + acc + b) = a + (l.map f).foldl max acc + b
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons,
      show max (a + acc + b) (a + f x + b) = a + max acc (f x) + b by omega]
    exact foldl_max_map_add f a b l _

theorem foldl_max_map_add0 {α : Type} (f : α → ℕ) (a b : ℕ) :
    ∀ (l : List α), l ≠ [] → (l.map fun x ↦ a + f x + b).foldl max 0 = a + (l.map f).foldl max 0 + b
  | x :: l, _ => by
    rw [List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons, Nat.zero_max, Nat.zero_max]
    exact foldl_max_map_add f a b l (f x)

/-- `osCF` is `osC`: the calls are the same at every rate (`Whir.osBody_rate`). -/
theorem osC_eq_fast (m : ℕ) : osC m = osCF m := by
  have hK (ri : ℕ) : B1.osKidsB B2C.fs wSBos (osCfgR m ri) = B1.osKidsB B2C.fs wSBos (osCfg m) := by
    unfold B1.osKidsB B1.osCallees
    rw [← osBody_rate]
  unfold osC osCF B1.osBos
  rw [fsFast_eq]
  simp only [hK]
  exact foldl_max_map_add0 _ _ _ _ (by decide)

/-- `osBosAt` at an arm is `osC`. -/
theorem osBosAt_eq {μ : ℕ} (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30) :
    B1.osBosAt B2C.fs wSBos μ = osC (μ - minOpenLog) := by
  have h : μ - minOpenLog < 11 := by simp only [minOpenLog] at h1 h2 ⊢; omega
  unfold B1.osBosAt osC openName openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, natStr_eq]

end
end LeanVM.Guest.Count
