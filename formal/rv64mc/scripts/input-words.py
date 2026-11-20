"""Write the guest's input words for a verifier fixture of `formal/lean_vm/scripts/export-verifier-fixtures-rust.sh`.

  python3 -I input-words.py FIXTURE_DIR OUT [--flip | --truncate]

OUT gets the input as little-endian 64-bit words, in the format `guest/src/main.rs` documents and the end statement's
`decodeInput` reads: the bytecode (count, words), the public input (4 words), the stream (count, 2 words per scalar),
the openings (phase count; per phase its path count; per path its leaf index, leaf length and words, sibling count and
4 words per sibling). `--flip` flips bit 0 of the first stream scalar, so the verifier rejects; `--truncate` drops the
last word, so the input is malformed.
"""

import struct
import sys
from pathlib import Path


def words_of(data: bytes) -> list[int]:
    if len(data) % 8:
        sys.exit("not a whole number of 64-bit words")
    return list(struct.unpack(f"<{len(data) // 8}Q", data))


def main() -> None:
    if len(sys.argv) < 3 or sys.argv[3:] not in ([], ["--flip"], ["--truncate"]):
        sys.exit(__doc__)
    fixture, out = Path(sys.argv[1]), Path(sys.argv[2])
    bytecode = words_of((fixture / "bytecode.bin").read_bytes())
    public_input = words_of((fixture / "public_input.bin").read_bytes())
    stream = words_of((fixture / "stream.bin").read_bytes())
    if len(public_input) != 4 or len(stream) % 2:
        sys.exit("unexpected public input or stream size")
    words = [len(bytecode), *bytecode, *public_input, len(stream) // 2, *stream]
    first_scalar = len(bytecode) + 1 + 4 + 1
    phases = (fixture / "merkle_phases.bin").read_bytes()
    pos = 0

    def take(fmt: str) -> int:
        nonlocal pos
        (value,) = struct.unpack_from(fmt, phases, pos)
        pos += struct.calcsize(fmt)
        return value

    n_phases = take("<I")
    words.append(n_phases)
    for _ in range(n_phases):
        n_paths = take("<I")
        words.append(n_paths)
        for _ in range(n_paths):
            words.append(take("<Q"))
            n_leaf = take("<I")
            words.append(n_leaf)
            words.extend(take("<Q") for _ in range(n_leaf))
            n_siblings = take("<I")
            words.append(n_siblings)
            words.extend(take("<Q") for _ in range(4 * n_siblings))
    if pos != len(phases):
        sys.exit("trailing bytes in merkle_phases.bin")
    if "--flip" in sys.argv:
        words[first_scalar] ^= 1
    if "--truncate" in sys.argv:
        words.pop()
    out.write_bytes(struct.pack(f"<{len(words)}Q", *words))


if __name__ == "__main__":
    main()
