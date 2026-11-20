# What the template generator can rely on in the guest's ELF

The guest links with `--emit-relocs` and `--no-relax` (`guest/build.rs`); `scripts/check-relocs.py ELF` checks every claim below and fails otherwise. On the image of the frozen build config:

- No relaxation: no `R_RISCV_RELAX` or `R_RISCV_ALIGN`, so every call is `auipc ra` (or `t1` for a tail call) followed by `jalr`, whatever the distance, and code size does not depend on layout.
- Every `auipc` in `.text` carries exactly one relocation, `R_RISCV_CALL_PLT` (1,584: a call, completed by the `jalr` right after it, which reads the `auipc`'s register) or `R_RISCV_PCREL_HI20` (150: an address), with one exception: a call from a function to its own entry (14, the recursive sorts and `clone_subtree`), which the assembler resolves itself. Such a call is a fixed offset within the function, so its template is `L.base`, not a callee field.
- Every `R_RISCV_PCREL_LO12_I` / `_S` (151) names the label of its `auipc`, reads the register that `auipc` wrote, and with it computes the `HI20`'s target. One `auipc` may have several `lo12` users (here one has two): a data reference is keyed by its `auipc`, with a list of users.
- Branches and `jal` carry no relocation, and none leaves its function (2,523 checked): the lift's labels are instruction indices, independent of layout.
- `.rodata` holds 147 `R_RISCV_64` absolute words (vtables of `Box<dyn Fn>`, panic locations), each equal to its target: the data image the link step checks depends on addresses through these words only.
- No jump tables (`-C jump-tables=no`): no `jalr` through a loaded address except the `Box<dyn Fn>` calls (23 `jalr` through `a*`/`s*` registers), which the crates rewrite removes.

The call site's two constants, the `auipc` value `hi` and the `jalr` offset `lo`, change whenever the distance to the callee changes, even for an unchanged caller, so a template takes each site as a field (`Site`) and its callee as another (`Callee`: index and entry), tied by `Site.WF` and `Callee.WF` (`Rv64mc/Link/Basic.lean`).
