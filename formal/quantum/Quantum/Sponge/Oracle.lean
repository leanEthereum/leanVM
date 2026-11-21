module

public import Quantum.Sponge.Oracle.Runtime
public import Quantum.Sponge.Oracle.Event

/-!
# Compressed oracles for the sponge's random functions

`Quantum.Sponge.Oracle.Runtime`: the three compressed oracles of `h`, `k`, `k'` and their
exactness against uniform functions (`Quantum.Sponge.evalDistMap_spongeCompressedRuntime`).
`Quantum.Sponge.Oracle.Event`: the bound on an upward-closed database event
(`Quantum.Sponge.rpow_inv_two_eventWeight_spongeCompressedRuntime_le`,
`Quantum.Sponge.eventWeight_spongeCompressedRuntime_le`).
-/
