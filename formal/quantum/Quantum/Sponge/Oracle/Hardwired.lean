module

public import Quantum.Sponge.Oracle.Hardwired.Mixed
public import Quantum.Sponge.Oracle.Hardwired.Runtime
public import Quantum.Sponge.Oracle.Hardwired.Event
public import Quantum.Sponge.Oracle.Hardwired.Average
public import Quantum.Sponge.Oracle.Hardwired.Read
public import Quantum.Sponge.Oracle.Hardwired.Classical
public import Quantum.Sponge.Oracle.Hardwired.Potential
public import Quantum.Sponge.Oracle.Hardwired.Reads

/-!
# The hardwired sponge runtime

* `Hardwired.Mixed`: the event bound for runtimes with quantum and classical ports.
* `Hardwired.Runtime`: hardwired cells `Hw`, the register `HwReg X Z M`, the classical read and
  program ports, runtime 1 `spongeHardwiredReadRuntime` and `spongeHardwiredRuntime`.
* `Hardwired.Event`: the graded event bound `eventWeight_spongeHardwiredRuntime_le`.
* `Hardwired.Average`: the hardwired runtime is the average over consistent functions
  (`evalDistMap_hardwired_eq_avg`, `evalDistMap_hardwired_eq_avg_consistent`).
* `Hardwired.Read`: the read-port certificate (`posSemidef_read_certificate`,
  `potential_hwReadKraus_le`, `potential_hwProgKraus_le`).
* `Hardwired.Classical`: the read ports are classical reads of consistent functions
  (`read_port_eq_classical_read`).
* `Hardwired.Potential`: one-cell Lipschitz diagonal potentials (`diagonalPotential_drop`).
* `Hardwired.Reads`: classical reads with hardwired cells (`withReads_hardwired_le`).
-/
