"""The pack of a function's generated data, as `LeanVM/Guest/PackHash.lean` computes it: 32-bit
FNV-1a over the stable name's UTF-8 bytes, mod the family's pack count."""


def fnv1a32(s):
    h = 2166136261
    for b in s.encode('utf-8'):
        h = (h ^ b) * 16777619 % 4294967296
    return h


def pack_of(key, k=64):
    return fnv1a32(key) % k
