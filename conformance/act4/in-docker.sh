#!/bin/sh
# generate.sh's work inside the image: ACT4 builds the tests (Sail running each one
# to record the expected values the self-checking build embeds) into /out.
set -eu
# Of the other tests ACT4 would select for this configuration, Zicsr's need CSRs, which
# leanVM does not have (the configuration claims Zicsr only for UDB to define MXLEN),
# and Zmmul's are M's multiplication tests again.
/act4/.venv/bin/act /config/test_config.yaml --workdir /act4/work --test-dir tests --extensions I,M --fast
cp -r /act4/work/leanvm-rv64im/elfs/rv64i/I /act4/work/leanvm-rv64im/elfs/rv64i/M /out/
for elf in /out/I/*.elf /out/M/*.elf; do
  # The symbol naming the compiler's temporary object file, whose name is random.
  riscv64-unknown-elf-objcopy --wildcard --strip-symbol='cc*.o' "$elf"
  # ACT4 switches compressed instructions on around its alignment padding, which marks
  # the file as using them (e_flags = EF_RISCV_RVC) though no instruction is compressed.
  test "$(od -An -tu4 -j48 -N4 "$elf" | tr -d ' ')" = 1
  printf '\000' | dd of="$elf" bs=1 seek=48 conv=notrunc status=none
done
chown -R "$OWNER" /out/I /out/M
