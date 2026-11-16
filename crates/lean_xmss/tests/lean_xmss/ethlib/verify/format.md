# Test format: leanXMSS verification

Check a signature of a 32-byte message under a public key.

## Test case format

```yaml
input:
  public_key: Bytes32 -- the public key
  message: Bytes32 -- the message
  signature: Bytes2404 -- the signature, which carries its leaf index
output: bool | null -- whether the signature verifies, or null when the input is rejected
```

All bytes are hex strings prefixed with `0x`.

## Condition

Inputs of any other length are rejected.

A signature verifies when both layers' digests are codewords, and the top layer's path reaches the root of the public key.

Each case named `tampered` flips one bit in the first value of one field of one layer.

Each case named `zeroed` sets the first message byte, or the last sibling of the top layer, to zero.

The case `verify_next_leaf_index` changes the leaf index of the signature to the next leaf.

A digest has 64 digits of 2 bits each.
It is a codeword when its last 6 digits are zero and its first 58 sum to 106.
Each case named `digit` signs one layer of the valid signature again, under a randomizer whose digest is not a codeword.
Its 58 chain values are those of the same key at the digits of that digest.
So the leaf, the path and the root do not change.
The codeword check of that layer is then the only check that rejects the signature.
The name gives the layer, `bottom` or `top`, and the digits of the digest:

| Name | Digits 58 to 63 | Sum of digits 0 to 57 |
| --- | --- | --- |
| `digit_sum_105` | all zero | 105 |
| `digit_sum_107` | all zero | 107 |
| `digit_58_nonzero` | digit 58 is 1, the others are zero | 106 |
| `digit_58_all_sum_106` | digit 58 is 1, the others are zero | 105 |
| `last_digit_nonzero` | digit 63 is 2, the others are zero | 106 |
| `last_digit_all_sum_106` | digit 63 is 2, the others are zero | 104 |

In the two rows named `all_sum_106`, the 64 digits of the digest sum to 106.

The case `verify_wrong_root_last_byte` flips the low bit of the last byte of the root.
The case `verify_wrong_root_high_bit` flips the high bit of its first byte.

The case `verify_zero_inputs` has a public key, a message and a signature of zero bytes.
Each case named `zero_root` has a public key whose root is zero, with the public parameter of the valid key.
Its signature has one bit flipped in the randomizer of one layer, so the digest of that layer is not a codeword.

The valid cases come from the `sign` cases, and the public keys from the `key_gen` cases.
The chain values of the cases named `digit` come from the seed of `key_gen_known_answer`.
