#!/bin/bash
# Task 1: build and run the encoder checks and the singular-minor counts.
cd "$(dirname "$0")"; mkdir -p 69_bin
for fb in 8 16 64; do cc -O2 -DFB=$fb 69_t1_encoder.c -o 69_bin/t1_$fb || exit 1; done
./69_bin/t1_64 3 1 SSS 20 1; ./69_bin/t1_64 4 2 SSSS 5 2; ./69_bin/t1_16 4 1 SSSS 200 3; ./69_bin/t1_8 3 2 SSS 2000 4
run() { ./69_bin/t1_$1 $2 $3 $4 $5 7; }
for fb in 8 16; do
  big=4000; [ $fb = 16 ] && big=40000
  run $fb 2 1 22 $big; run $fb 2 1 11 $big; run $fb 2 2 22 $big
  run $fb 3 1 222 $((big/20)); run $fb 3 1 111 $((big/20))
  run $fb 4 1 2222 2000; run $fb 4 1 1111 2000; run $fb 5 1 22222 2000; run $fb 3 2 222 2000
done
./69_bin/t1_64 3 1 222 20 5; ./69_bin/t1_64 4 1 1111 2000 5; ./69_bin/t1_64 5 1 22222 500 6
