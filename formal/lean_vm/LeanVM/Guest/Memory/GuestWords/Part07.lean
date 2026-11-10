module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_319 : wStaticRange 319 1 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_320_0 : noTopRet ((Data.core320.body.drop 0).take 1627) = true ∧
    blockR (wlookJ 320) (womLookJ 320) true [(.n 13, 8), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1644, 156), (.n 1646, 6), (.n 2188, 7)] Data.core320.params Data.core320.name ((Data.core320.body.drop 0).take 1627)
      ([], []) = some (⟨225906, []⟩, []) ∧
    blockEnv true [(.n 13, 8), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1644, 156), (.n 1646, 6), (.n 2188, 7)] Data.core320.params ([], []) ((Data.core320.body.drop 0).take 1627) = ([(.n 1646, 6), (.n 1644, 156), (.n 1427, 5), (.n 1405, 64), (.n 1280, 64), (.n 1053, 64), (.n 826, 64), (.n 599, 64), (.n 376, 64), (.n 159, 24), (.n 157, 156), (.n 27, 128), (.n 25, 1404), (.n 23, 1404), (.n 21, 6), (.n 19, 6), (.n 17, 26), (.n 15, 12), (.n 13, 8)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_320_1627 : blockR (wlookJ 320) (womLookJ 320) true [(.n 13, 8), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1644, 156), (.n 1646, 6), (.n 2188, 7)] Data.core320.params Data.core320.name (Data.core320.body.drop 1627)
    ([(.n 1646, 6), (.n 1644, 156), (.n 1427, 5), (.n 1405, 64), (.n 1280, 64), (.n 1053, 64), (.n 826, 64), (.n 599, 64), (.n 376, 64), (.n 159, 24), (.n 157, 156), (.n 27, 128), (.n 25, 1404), (.n 23, 1404), (.n 21, 6), (.n 19, 6), (.n 17, 26), (.n 15, 12), (.n 13, 8)], []) = some (⟨33892, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_321_0 : noTopRet ((Data.core321.body.drop 0).take 1627) = true ∧
    blockR (wlookJ 321) (womLookJ 321) true [(.n 13, 16), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1656, 156), (.n 1658, 6), (.n 2242, 7)] Data.core321.params Data.core321.name ((Data.core321.body.drop 0).take 1627)
      ([], []) = some (⟨228866, []⟩, []) ∧
    blockEnv true [(.n 13, 16), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1656, 156), (.n 1658, 6), (.n 2242, 7)] Data.core321.params ([], []) ((Data.core321.body.drop 0).take 1627) = ([(.n 1658, 6), (.n 1656, 156), (.n 1427, 5), (.n 1405, 64), (.n 1280, 64), (.n 1053, 64), (.n 826, 64), (.n 599, 64), (.n 376, 64), (.n 159, 24), (.n 157, 156), (.n 27, 128), (.n 25, 1404), (.n 23, 1404), (.n 21, 6), (.n 19, 6), (.n 17, 26), (.n 15, 12), (.n 13, 16)], []) := by
  decide +kernel

end
end LeanVM.Guest
