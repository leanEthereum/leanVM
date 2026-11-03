# Test format: leanSPHINCS key generation

Derive a leanSPHINCS public key from a 32-byte seed.

## Test case format

```yaml
input:
  seed: Bytes32 -- the secret seed S_0
output: Bytes32 | null -- the public key, or null when the input is rejected
```

All bytes are hex strings prefixed with `0x`.

Every secret derives from the scheme seed `S = H("leanSPHINCS" | S_0)`, not from `S_0` itself.

The public key is the root of the top tree, then the public parameter:

```text
    [ root: 16 | public parameter: 16 ]
```

## Condition

A seed of any length other than 32 bytes is rejected.

These cases pin the key derivation of the specification, so two implementations of it agree byte for byte.
