module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_304 : kvxStaticRange 304 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_305 : kvxStaticRange 305 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_306_0 : noTopRet ((Data.core306.body.drop 0).take 1320) = true ∧
    blockR (kvxlookJ 306) (kvxomLookJ 306) false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core306.params Data.core306.name ((Data.core306.body.drop 0).take 1320)
      ([], []) = some (⟨40147, []⟩, []) ∧
    blockEnv false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core306.params ([], []) ((Data.core306.body.drop 0).take 1320) = ([(.n 1258, 18), (.n 1207, 2), (.n 1206, 0), (.n 1120, 23), (.n 1067, 3), (.n 1066, 0), (.n 878, 32), (.n 827, 4), (.n 826, 0), (.n 638, 56), (.n 585, 7), (.n 584, 0), (.n 396, 112), (.n 348, 25), (.n 347, 0)], []) := by
  decide +kernel

end
end LeanVM.Guest
