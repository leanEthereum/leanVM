import LeanVM.Guest.B1.Bits.GPowerP
import LeanVM.Guest.B1.Sig.SpWotsData
import LeanVM.Guest.B1.Sig.SpWotsData0
import LeanVM.Guest.B1.Sig.SpWotsData1
import LeanVM.Guest.B1.Sig.SphincsData
import LeanVM.Guest.B1.Sig.SphincsData0
import LeanVM.Guest.B1.Sig.SphincsData1
import LeanVM.Guest.B1.Sig.SphincsData2
import LeanVM.Guest.B1.Sig.SphincsDigestData
import LeanVM.Guest.B1.Sig.XmssSegData
import LeanVM.Guest.B1.Sig.XmssSegData1
import LeanVM.Guest.B1.Sig.XmssSegData10
import LeanVM.Guest.B1.Sig.XmssSegData11
import LeanVM.Guest.B1.Sig.XmssSegData12
import LeanVM.Guest.B1.Sig.XmssSegData13
import LeanVM.Guest.B1.Sig.XmssSegData14
import LeanVM.Guest.B1.Sig.XmssSegData15
import LeanVM.Guest.B1.Sig.XmssSegData16
import LeanVM.Guest.B1.Sig.XmssSegData17
import LeanVM.Guest.B1.Sig.XmssSegData18
import LeanVM.Guest.B1.Sig.XmssSegData19
import LeanVM.Guest.B1.Sig.XmssSegData2
import LeanVM.Guest.B1.Sig.XmssSegData20
import LeanVM.Guest.B1.Sig.XmssSegData21
import LeanVM.Guest.B1.Sig.XmssSegData22
import LeanVM.Guest.B1.Sig.XmssSegData23
import LeanVM.Guest.B1.Sig.XmssSegData24
import LeanVM.Guest.B1.Sig.XmssSegData25
import LeanVM.Guest.B1.Sig.XmssSegData26
import LeanVM.Guest.B1.Sig.XmssSegData27
import LeanVM.Guest.B1.Sig.XmssSegData28
import LeanVM.Guest.B1.Sig.XmssSegData29
import LeanVM.Guest.B1.Sig.XmssSegData3
import LeanVM.Guest.B1.Sig.XmssSegData30
import LeanVM.Guest.B1.Sig.XmssSegData31
import LeanVM.Guest.B1.Sig.XmssSegData32
import LeanVM.Guest.B1.Sig.XmssSegData33
import LeanVM.Guest.B1.Sig.XmssSegData34
import LeanVM.Guest.B1.Sig.XmssSegData4
import LeanVM.Guest.B1.Sig.XmssSegData5
import LeanVM.Guest.B1.Sig.XmssSegData6
import LeanVM.Guest.B1.Sig.XmssSegData7
import LeanVM.Guest.B1.Sig.XmssSegData8
import LeanVM.Guest.B1.Sig.XmssSegData9

/-! **B1's per-function proofs read their own function's core module alone.** A proof stated for
every program that finds its function (`Finds`, `CoreFind.lean`), or a check of one function's
body, imports the core module holding that function (its pack, `Guest/Pack/P<k>/Core.lean`, or its
own, `Guest/Pack/<key>/Core*.lean`) and no other core IR: not the glue (`Data.Core`, `CoreData`,
`Data.Names`, `CoreNames`), not another pack (the names, `Data.NameStrings`, are allowed). So an
edit of one function rebuilds the proofs of its pack and the glue, not the others' proofs. This
module fails to build if a listed module's imports reach other core IR. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let idx : Std.HashMap Name Nat := (names.zipIdx.toList).foldl (fun m (n, i) => m.insert n i) {}
  let closure (m : Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo := [m]
    while !todo.isEmpty do
      let x := todo.head!
      todo := todo.tail!
      for i in (idx.get? x).map (data[·]!.imports) |>.getD #[] do
        unless seen.contains i.module do
          seen := seen.insert i.module
          todo := i.module :: todo
    return seen
  -- each per-function proof, with the functions whose core modules it may read
  let proofs : List (Name × List Name) := [
    (`LeanVM.Guest.B1.Bits.GPowerP, [`g_power_of_word]),
    (`LeanVM.Guest.B1.Sig.SpWotsData, [`sp_wots]),
    (`LeanVM.Guest.B1.Sig.SpWotsData0, [`sp_wots]),
    (`LeanVM.Guest.B1.Sig.SpWotsData1, [`sp_wots]),
    (`LeanVM.Guest.B1.Sig.SphincsData, [`verify_sig_lean_sphincs]),
    (`LeanVM.Guest.B1.Sig.SphincsData0, [`verify_sig_lean_sphincs]),
    (`LeanVM.Guest.B1.Sig.SphincsData1, [`verify_sig_lean_sphincs]),
    (`LeanVM.Guest.B1.Sig.SphincsData2, [`verify_sig_lean_sphincs]),
    (`LeanVM.Guest.B1.Sig.SphincsDigestData, [`verify_sig_lean_sphincs]),
    (`LeanVM.Guest.B1.Sig.XmssSegData, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData1, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData10, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData11, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData12, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData13, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData14, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData15, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData16, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData17, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData18, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData19, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData2, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData20, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData21, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData22, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData23, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData24, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData25, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData26, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData27, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData28, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData29, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData3, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData30, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData31, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData32, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData33, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData34, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData4, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData5, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData6, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData7, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData8, [`main_loop2]),
    (`LeanVM.Guest.B1.Sig.XmssSegData9, [`main_loop2])]
  let glue := [`LeanVM.Guest.Data.Core, `LeanVM.Guest.Data.Names, `LeanVM.Guest.CoreData,
    `LeanVM.Guest.CoreNames]
  -- a core module, and the one that holds function `k`
  let isCore (d : Name) : Bool := (`LeanVM.Guest.Pack).isPrefixOf d && match d with
    | .str _ s => s.startsWith "Core"
    | _ => false
  let home (k : Name) : Option Name :=
    (env.getModuleIdxFor? (`LeanVM.Guest.Fn ++ k ++ `core)).map (names[·.toNat]!)
  for (m, keys) in proofs do
    let bad := (closure m).toList.filter fun d ↦ glue.any (·.isPrefixOf d) ||
      (isCore d && !keys.any fun k ↦ (`LeanVM.Guest.Pack ++ k).isPrefixOf d || home k == some d)
    unless bad.isEmpty do
      throwError m!"{m} imports {bad}: a per-function proof reads its own function's core module \
        only (see `LeanVM/Guest/B1/FnFirewall.lean`)"
