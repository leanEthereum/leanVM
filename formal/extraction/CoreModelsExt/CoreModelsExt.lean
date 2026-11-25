-- Models of Rust standard library items the extractions use and the pinned hax Lean library
-- (CoreModels) lacks, one module per area, shared by every extraction. A `def` mirrors the Rust;
-- an `opaque` is an assumption about an item whose body is not modelled. Each is a candidate
-- for upstreaming to CoreModels.
module
public import CoreModelsExt.Numbers
public import CoreModelsExt.Core
public import CoreModelsExt.Iterators
public import CoreModelsExt.Slices
public import CoreModelsExt.Memory
public import CoreModelsExt.Strings
public import CoreModelsExt.Collections
public import CoreModelsExt.Sync
