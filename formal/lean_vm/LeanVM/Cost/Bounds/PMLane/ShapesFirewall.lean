import LeanVM.Cost.Bounds.PMLane.Shapes

/-! **The decoder's shape checks read numbers alone.** `PMLane/Shapes`' `60` kernel evaluations
take the longest of the cost bounds, and a module is rebuilt whenever anything it imports changes.
So they import only the functions they evaluate (the extractor's parameter search,
`LeanVM.Protocol.Extraction.Extractor`), the bounds as definitions
(`Bounds/Decoder/ShapeDefs.lean`, `Bounds/PMBasis/{Defs,LaneDefs,Values}.lean`,
`Bounds/PMLane/{InterpDefs,ShapeDefs}.lean`) and the prices they are checked against (`Cost/Prices.lean`,
definitions over the statement alone), none of the cost compiler, the compiled extractor or the
bounds' proofs: an edit there rebuilds no check. This module, which imports the checks alone,
fails to build if their imports reach any other `LeanVM.Cost` module. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [`LeanVM.Cost.Bounds.Decoder.ShapeDefs, `LeanVM.Cost.Bounds.PMBasis.Defs,
    `LeanVM.Cost.Bounds.PMBasis.LaneDefs, `LeanVM.Cost.Bounds.PMBasis.Values,
    `LeanVM.Cost.Bounds.PMLane.InterpDefs, `LeanVM.Cost.Bounds.PMLane.ShapeDefs,
    `LeanVM.Cost.Bounds.PMLane.Shapes, `LeanVM.Cost.Prices]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦
    (`LeanVM.Cost).isPrefixOf m && !allowed.contains m
  unless reached.isEmpty do
    throwError m!"the decoder's shape checks import {reached.toList}: keep the definitions they \
      evaluate in modules that do not (see `Bounds/PMLane/ShapesFirewall.lean`)"
