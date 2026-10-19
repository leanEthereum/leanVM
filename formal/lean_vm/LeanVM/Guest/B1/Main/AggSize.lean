/-
  LeanVM.Guest.B1.Main.AggSize

  The sizes of the valid trees of `aggregate_claims`' callees: its five loops over the children,
  each its frames, and its two batched sumchecks, each its frame.
-/

module

public import LeanVM.Guest.B1.Main.AggPlaced
public import LeanVM.Guest.B1.Main.LoopAt

/-!
# The sizes of `aggregate_claims`' callees

`__loop95` to `__loop99` are `mul_range` loops over the `n` children with no callee and no
`HeapBuf` (`leafLoop_total`): `n + 1` frames. `batch_sumcheck__L22`, `batch_sumcheck__L28` are
straight-line with no callee and no `HeapBuf` (`vtc_leaf_total`): one frame.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (vtc_leaf_total)

@[expose] public section

variable {fs : String → ℕ} {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E}

theorem core566_split : Fn.body Data.core566 = (Fn.body Data.core566).take 2130 ++
    [.callIf (.n 2453) "__loop95" [.n 2455, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem core567_split : Fn.body Data.core567 = (Fn.body Data.core567).take 57 ++
    [.callIf (.n 55) "__loop96" [.n 57, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem core569_split : Fn.body Data.core569 = (Fn.body Data.core569).take 262 ++
    [.callIf (.n 265) "__loop97" [.n 267, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem core570_split : Fn.body Data.core570 = (Fn.body Data.core570).take 77 ++
    [.callIf (.n 74) "__loop98" [.n 76, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem core572_split : Fn.body Data.core572 = (Fn.body Data.core572).take 1192 ++
    [.callIf (.n 1196) "__loop99" [.n 1198, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem core568_split : Fn.body Data.core568 = (Fn.body Data.core568).take 1061 ++
    [.ret [.n 1129, .n 1130, .n 1131]] :=
  stmtsEqb_sound (by decide +kernel)

theorem core571_split : Fn.body Data.core571 = (Fn.body Data.core571).take 1349 ++
    [.ret [.n 1435, .n 1436, .n 1437]] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop95_total (hm : 0 < m) (hn : t.name = "__loop95")
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop95" + fs "__loop95" :=
  leafLoop_total find_loop95 core566_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 2125 rfl) (mem_of_getElem? 2126 rfl) (mem_of_getElem? 2127 rfl)
    (mem_of_getElem? 2128 rfl) (mem_of_getElem? 2129 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop96_total (hm : 0 < m) (hn : t.name = "__loop96")
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop96" + fs "__loop96" :=
  leafLoop_total find_loop96 core567_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 52 rfl) (mem_of_getElem? 53 rfl) (mem_of_getElem? 54 rfl)
    (mem_of_getElem? 55 rfl) (mem_of_getElem? 56 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop97_total (hm : 0 < m) (hn : t.name = "__loop97")
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop97" + fs "__loop97" :=
  leafLoop_total find_loop97 core569_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 257 rfl) (mem_of_getElem? 258 rfl) (mem_of_getElem? 259 rfl)
    (mem_of_getElem? 260 rfl) (mem_of_getElem? 261 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop98_total (hm : 0 < m) (hn : t.name = "__loop98")
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop98" + fs "__loop98" :=
  leafLoop_total find_loop98 core570_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 72 rfl) (mem_of_getElem? 73 rfl) (mem_of_getElem? 74 rfl)
    (mem_of_getElem? 75 rfl) (mem_of_getElem? 76 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop99_total (hm : 0 < m) (hn : t.name = "__loop99")
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop99" + fs "__loop99" :=
  leafLoop_total find_loop99 core572_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 1187 rfl) (mem_of_getElem? 1188 rfl) (mem_of_getElem? 1189 rfl)
    (mem_of_getElem? 1190 rfl) (mem_of_getElem? 1191 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem bs22_total {args : List E} (hn : t.name = "batch_sumcheck__L22")
    (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs "batch_sumcheck__L22" :=
  vtc_leaf_total find_bs22 core568_split (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hn hv hbo

set_option maxRecDepth 100000 in
theorem bs28_total {args : List E} (hn : t.name = "batch_sumcheck__L28")
    (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs "batch_sumcheck__L28" :=
  vtc_leaf_total find_bs28 core571_split (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hn hv hbo

/-- **`aggregate_claims`' bound** over `n` children: its frame and `HeapBuf`s, its five loops'
frames and its two sumchecks' frames. -/
def aggBound (fs : String → ℕ) (n : ℕ) : ℕ :=
  fs "aggregate_claims" + (aggSizes n).sum + ((n * fs "__loop95" + fs "__loop95") +
    ((n * fs "__loop96" + fs "__loop96") + (fs "batch_sumcheck__L22" + ((n * fs "__loop97" +
      fs "__loop97") + ((n * fs "__loop98" + fs "__loop98") + (fs "batch_sumcheck__L28" +
        (n * fs "__loop99" + fs "__loop99")))))))

end
end LeanVM.Guest.B1.Main
