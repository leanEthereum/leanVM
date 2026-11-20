# Running the end statement's own machine

`Sound image` (`Rv64mc/EndStatement.lean`) is an implication from `Loaded image words s` and `Halts s n 0`. It would hold trivially if no loaded state ever halted with `a0 = 0`: if the machine trapped on an instruction it does not model, on an access outside its windows, or on a load of input placed where the guest does not look. `AllDecode image` rules out the first kind statically. The others are ruled out by running the statement's definitions on real inputs and watching all three verdicts appear: `0` on an honest proof, `1` on a mutated one, `2` on a truncated one.

## The runner

`lake exe rv64mc-run ELF WORDS [--verify] [--fuel N]` (`RunImage.lean`):

1. reads the ELF into the statement's `Image` with `Rv64mc.readImage` (`Rv64mc/ImageOfElf.lean`), the reader that also defines the end theorem's `image` (`Rv64mc/Gen/Image.lean`), so the two cannot differ;
2. prints `AllDecode` computed on those words with riscv-zkvm's `decode`, the definition the statement uses (the end theorem proves it in the kernel, `Rv64mc/Final/End.lean`);
3. builds a state with the data words, the input words at `inputBase`, `a0` their number and every other register and word zero, and checks every clause of `Loaded` on it: `pc`, the code map against `Image.codeAt` at every code address and one past the end, every data word, every input word, `a0`, the capacity;
4. prints `decodeInput words` and, with `--verify`, the statement's `verify` on what it decodes;
5. runs the statement's `step` until it returns `none`, and prints whether the state it stopped in satisfies `Halts`'s last clauses (an `ECALL` at `pc`, `t0 = 0`) and its `a0`.

The state is held in a hash map and an array (riscv-zkvm's `ExecState`), and each step applies `Rv64mc.step` to the `MachineState` they stand for (`ExecState.toMachineState`), then copies back the 32 registers, the `pc` and the doublewords the instruction can write (`ExecState.writtenAddrs`: the one containing doubleword of a store; `step` executes no `ECALL` or `CSRS`). This is extensionally the statement's `steps`, by the argument riscv-zkvm's `Interpreter/State.lean` gives for its own loop, not by a theorem: a dropped write would show up as a wrong verdict, not as a silent success.

## Inputs

`scripts/input-words.py FIXTURE OUT [--flip | --truncate]` writes the guest's input words for a fixture of `formal/lean_vm/scripts/export-verifier-fixtures-rust.sh` (`bytecode.bin`, `public_input.bin`, `stream.bin`, `merkle_phases.bin`, the honest proofs of the Rust prover). `--flip` flips bit 0 of the first stream scalar, `--truncate` drops the last word.

```bash
formal/lean_vm/scripts/export-verifier-fixtures-rust.sh FIX
cd formal/rv64mc && lake build rv64mc-run
python3 -I scripts/input-words.py FIX/fibonacci-rate4 fib.words
python3 -I scripts/input-words.py FIX/fibonacci-rate4 fib-flip.words --flip
python3 -I scripts/input-words.py FIX/fibonacci-rate4 fib-trunc.words --truncate
.lake/build/bin/rv64mc-run out/canon.elf fib.words --verify        # run: halted, a0 = 0; verify: true
.lake/build/bin/rv64mc-run out/canon.elf fib-flip.words --verify   # run: halted, a0 = 1; verify: false
.lake/build/bin/rv64mc-run out/canon.elf fib-trunc.words           # run: halted, a0 = 2; decodeInput: none
```

The expected lines are what the guest's verdicts mean (`guest/src/main.rs`). A CI job and every benchmark binary should run the three.

## Results

On the image whose sha256 is `8cb4e7b8…` (`image.sha256`), with the fixtures of `formal/lean_vm/scripts/export-verifier-fixtures-rust.sh` on this tree. On every one `AllDecode` and every clause of `Loaded` held; honest inputs decoded, the statement's `verify` accepted them and the run halted with `a0 = 0`; the flipped inputs decoded, `verify` rejected them and the run halted with `a0 = 1`; the truncated ones did not decode and the run halted with `a0 = 2`. Steps of the statement's machine:

| fixture | input words | honest (a0 = 0) | flipped (a0 = 1) | truncated (a0 = 2) |
| --- | --- | --- | --- | --- |
| fibonacci-rate4 | 16,664 | 127,045,937 | 2,600,063 | 1,667,432 |
| conditionals-rate2 | 24,906 | 154,632,148 | 4,009,179 | 3,076,546 |
| chain1000-rate3 | 24,044 | 159,582,002 | 4,071,083 | 3,137,094 |
| chain4-rate1 | 38,700 | 204,975,556 | 4,334,868 | 3,402,212 |

The runner steps about 140,000 instructions a second; the honest runs take 15 to 25 CPU-minutes each.

## The Model mirror

`lake exe rv64mc-model WORDS` (`RunModel.lean`) decodes the input with the statement's `decodeInput` and prints `mainVerdictRust` (`Rv64mc/Model/Walk.lean`, the Lean mirror of `main`'s verdict, `ACCEPT` as `true`) next to the statement's `verify`. `mainVerdictRust_sound` proves that the first implies the second; running both on real inputs shows that the mirror is not vacuous, that it accepts honest proofs as the guest does.

On the twelve inputs above (four fixtures, each honest, flipped and truncated): every honest input decoded with `mainVerdictRust: true` and `verify: true`, every flipped input decoded with `mainVerdictRust: false` and `verify: false`, and every truncated input gave `decodeInput: none`.

## What it does not show

It shows that the hypotheses of `Sound` are met by real runs and that the statement's `decodeInput` and `verify` agree with the guest on them; it does not show that they are met by every accepted proof (that would be completeness, not stated). The state it builds is one loaded state; `Sound` quantifies over all of them, which only makes it stronger.
