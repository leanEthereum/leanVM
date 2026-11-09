/-
  LeanVM.Guest.B1.Whir.FactsAll

  Every candidate's facts.
-/

module

public import LeanVM.Guest.B1.Whir.Facts0
public import LeanVM.Guest.B1.Whir.Facts1
public import LeanVM.Guest.B1.Whir.Facts2
public import LeanVM.Guest.B1.Whir.Facts3
public import LeanVM.Guest.B1.Whir.Facts4
public import LeanVM.Guest.B1.Whir.Facts5
public import LeanVM.Guest.B1.Whir.Facts6
public import LeanVM.Guest.B1.Whir.Facts7
public import LeanVM.Guest.B1.Whir.Facts8
public import LeanVM.Guest.B1.Whir.Facts9
public import LeanVM.Guest.B1.Whir.Facts10
public import LeanVM.Guest.B1.Whir.Facts11
public import LeanVM.Guest.B1.Whir.Facts12
public import LeanVM.Guest.B1.Whir.Facts13
public import LeanVM.Guest.B1.Whir.Facts14
public import LeanVM.Guest.B1.Whir.Facts15
public import LeanVM.Guest.B1.Whir.Facts16
public import LeanVM.Guest.B1.Whir.Facts17
public import LeanVM.Guest.B1.Whir.Facts18
public import LeanVM.Guest.B1.Whir.Facts19
public import LeanVM.Guest.B1.Whir.Facts20
public import LeanVM.Guest.B1.Whir.Facts21
public import LeanVM.Guest.B1.Whir.Facts22
public import LeanVM.Guest.B1.Whir.Facts23
public import LeanVM.Guest.B1.Whir.Facts24
public import LeanVM.Guest.B1.Whir.Facts25
public import LeanVM.Guest.B1.Whir.Facts26
public import LeanVM.Guest.B1.Whir.Facts27

/-!
# The 28 candidates' facts

`candB_all`: for every stack log `22 ≤ μ ≤ 28` and rate `1 ≤ r ≤ 4`, the candidate
`candidate μ r` has its facts (`Whir/Facts{m}.lean`).
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

theorem candB_all (μ r : ℕ) (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    candB (candidate μ r) μ r = true := by
  interval_cases μ <;> interval_cases r
  · exact candB_0
  · exact candB_7
  · exact candB_14
  · exact candB_21
  · exact candB_1
  · exact candB_8
  · exact candB_15
  · exact candB_22
  · exact candB_2
  · exact candB_9
  · exact candB_16
  · exact candB_23
  · exact candB_3
  · exact candB_10
  · exact candB_17
  · exact candB_24
  · exact candB_4
  · exact candB_11
  · exact candB_18
  · exact candB_25
  · exact candB_5
  · exact candB_12
  · exact candB_19
  · exact candB_26
  · exact candB_6
  · exact candB_13
  · exact candB_20
  · exact candB_27

end
end LeanVM.Guest.B1.Whir
