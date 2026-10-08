use leanvm_verus::gf2_8 as v8;
use leanvm_verus::phi8_tower as verified;
use primitives::field as production;

/// Every byte: the table and `phi8_192` (domain of 256 elements, so exhaustive).
#[test]
fn table_and_embedding_match() {
    for a in 0..=255u8 {
        let (v, p) = (verified::phi8_192(v8::F8(a)), production::phi8_192(production::F8(a)));
        assert_eq!((v.c0, v.c1, v.c2), (p.c0, p.c1, p.c2), "phi8_192({a:#04x})");
        let (tv, tp) = (
            verified::PHI_8_TABLE_192[a as usize],
            production::PHI_8_TABLE_192[a as usize],
        );
        assert_eq!((tv.c0, tv.c1, tv.c2), (tp.c0, tp.c1, tp.c2), "PHI_8_TABLE_192[{a}]");
    }
}
