#!/bin/bash
# Task 4: rank-one tensor lists, checked by encoding. Builds the three field variants.
cd "$(dirname "$0")"; mkdir -p 69_bin
for fb in 8 16 64; do cc -O2 -DFB=$fb 69_t4_product.c -o 69_bin/t4_product_$fb || exit 1; done
p() { ./69_bin/t4_product_$1 $2 $3 $4 $5 $6 $7 | sed 's/generalized Singleton bound on the minimum for [0-9]* members/gS bound/; s/(kernel dim of B 1, //; s/)//'; }
p 64 4 1 3 6 1 2222; p 64 5 1 4 6 1 22222; p 64 5 1 3 70 1 22222; p 64 6 1 4 70 1 222222; p 64 6 1 3 200 1 222222
p 64 7 1 5 70 1 2222222; p 64 7 1 4 2000 1 2222222
p 64 4 2 3 28 1 2222; p 64 5 2 4 28 1 22222; p 64 5 2 3 1820 1 22222
p 64 6 1 4 70 1 111111; p 64 6 1 4 70 1 SSSSSS; p 16 6 1 4 70 1 222222; p 8 6 1 4 70 1 222222; p 8 5 2 4 28 3 22222
