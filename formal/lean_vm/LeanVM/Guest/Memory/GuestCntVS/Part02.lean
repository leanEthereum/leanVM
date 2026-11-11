module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_318 : kvsStaticRange 318 13 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_331 : kvsStaticRange 331 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_332 : kvsStaticRange 332 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_333_0 : noTopRet ((Data.core333.body.drop 0).take 1428) = true ∧
    blockR (kvslookJ 333) (kvsomLookJ 333) false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 649, 1), (.n 650, 3), (.n 704, 23), (.n 782, 1), (.n 783, 3), (.n 830, 20), (.n 1377, 0), (.n 1378, 27), (.n 1661, 0), (.n 1662, 6), (.n 2383, 0), (.n 2384, 4), (.n 2405, 0), (.n 2406, 2)] Data.core333.params Data.core333.name ((Data.core333.body.drop 0).take 1428)
      ([], []) = some (⟨9250, []⟩, []) ∧
    blockEnv false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 649, 1), (.n 650, 3), (.n 704, 23), (.n 782, 1), (.n 783, 3), (.n 830, 20), (.n 1377, 0), (.n 1378, 27), (.n 1661, 0), (.n 1662, 6), (.n 2383, 0), (.n 2384, 4), (.n 2405, 0), (.n 2406, 2)] Data.core333.params ([], []) ((Data.core333.body.drop 0).take 1428) = ([(.n 1378, 27), (.n 1377, 0), (.n 830, 20), (.n 783, 3), (.n 782, 1), (.n 704, 23), (.n 650, 3), (.n 649, 1), (.n 538, 32), (.n 484, 5), (.n 483, 1), (.n 368, 55), (.n 314, 8), (.n 313, 1), (.n 196, 109), (.n 152, 37), (.n 151, 1)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_333_1428 : noTopRet ((Data.core333.body.drop 1428).take 1428) = true ∧
    blockR (kvslookJ 333) (kvsomLookJ 333) false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 649, 1), (.n 650, 3), (.n 704, 23), (.n 782, 1), (.n 783, 3), (.n 830, 20), (.n 1377, 0), (.n 1378, 27), (.n 1661, 0), (.n 1662, 6), (.n 2383, 0), (.n 2384, 4), (.n 2405, 0), (.n 2406, 2)] Data.core333.params Data.core333.name ((Data.core333.body.drop 1428).take 1428)
      ([(.n 1378, 27), (.n 1377, 0), (.n 830, 20), (.n 783, 3), (.n 782, 1), (.n 704, 23), (.n 650, 3), (.n 649, 1), (.n 538, 32), (.n 484, 5), (.n 483, 1), (.n 368, 55), (.n 314, 8), (.n 313, 1), (.n 196, 109), (.n 152, 37), (.n 151, 1)], []) = some (⟨184, []⟩, []) ∧
    blockEnv false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 649, 1), (.n 650, 3), (.n 704, 23), (.n 782, 1), (.n 783, 3), (.n 830, 20), (.n 1377, 0), (.n 1378, 27), (.n 1661, 0), (.n 1662, 6), (.n 2383, 0), (.n 2384, 4), (.n 2405, 0), (.n 2406, 2)] Data.core333.params ([(.n 1378, 27), (.n 1377, 0), (.n 830, 20), (.n 783, 3), (.n 782, 1), (.n 704, 23), (.n 650, 3), (.n 649, 1), (.n 538, 32), (.n 484, 5), (.n 483, 1), (.n 368, 55), (.n 314, 8), (.n 313, 1), (.n 196, 109), (.n 152, 37), (.n 151, 1)], []) ((Data.core333.body.drop 1428).take 1428) = ([(.n 2406, 2), (.n 2405, 0), (.n 2384, 4), (.n 2383, 0), (.n 1662, 6), (.n 1661, 0), (.n 1378, 27), (.n 1377, 0), (.n 830, 20), (.n 783, 3), (.n 782, 1), (.n 704, 23), (.n 650, 3), (.n 649, 1), (.n 538, 32), (.n 484, 5), (.n 483, 1), (.n 368, 55), (.n 314, 8), (.n 313, 1), (.n 196, 109), (.n 152, 37), (.n 151, 1)], []) := by
  decide +kernel

end
end LeanVM.Guest
