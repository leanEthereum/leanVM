//! The verification key: the constants of the Groth16 verifier contract at
//! `0x00000000003f3659fA84731896ba1C417b8F8A25` on World Chain (chain 480), which World ID 4.0's
//! `WorldIDVerifier` calls, with what the verifier derives from them at compile time.
//!
//! The contract checks `e(A, B) e(C, -delta) e(alpha, -beta) e(L, -gamma) = 1` with
//! `L = IC[0] + sum_i x_i IC[i + 1]` over the public inputs `x`, so it holds `-beta`, `-gamma`
//! and `-delta`, as this does.

use crate::Error;
use crate::curve::{G1Affine, G1Jacobian, G1Point, G2Affine, G2Point};
use crate::fp12::Fp12;
use crate::pairing::{N_LINES, NormalizedLine, miller_loop_prepared, normalize, prepare};

/// The public inputs a proof has.
pub const N_INPUTS: usize = 15;

pub const ALPHA: G1Point = G1Point {
    x: [
        0x65b3_b0db_d653_e2c7,
        0xffa0_8a9f_ae75_57b1,
        0xe8a4_d70b_de8c_1ccc,
        0x2452_29d9_b076_b3c0,
    ],
    y: [
        0x4b79_8d27_4a18_2302,
        0x7a00_0b4a_c6c8_6b2d,
        0x46e9_4b5e_fa33_73b4,
        0x253e_c859_88db_b84e,
    ],
};

pub const BETA_NEG: G2Point = G2Point {
    x: [
        [
            0xe133_a2bd_5e61_d244,
            0x26e1_7012_0aca_f441,
            0x685f_d507_05b2_8096,
            0x2424_bcc1_f60a_5472,
        ],
        [
            0x39ff_2797_8a29_a1db,
            0x208e_e8b3_487f_6f2b,
            0x9299_be24_705b_92cf,
            0x0709_0a82_e8fa_bbd3,
        ],
    ],
    y: [
        [
            0x4222_df29_38b4_e51e,
            0x7138_2cba_2b3c_4fdc,
            0xa340_91c5_d2c6_ded5,
            0x04dd_c8d3_0d5c_438c,
        ],
        [
            0xeb99_b23c_aa7f_bf1d,
            0x66c5_2eb8_3a95_9f79,
            0xf274_1f4f_4120_ddb4,
            0x2583_3b15_e156_ae01,
        ],
    ],
};

pub const GAMMA_NEG: G2Point = G2Point {
    x: [
        [
            0x46de_bd5c_d992_f6ed,
            0x6743_22d4_f75e_dadd,
            0x426a_0066_5e5c_4479,
            0x1800_deef_121f_1e76,
        ],
        [
            0x97e4_85b7_aef3_12c2,
            0xf1aa_4933_35a9_e712,
            0x7260_bfb7_31fb_5d25,
            0x198e_9393_920d_483a,
        ],
    ],
    y: [
        [
            0xef39_c015_7182_7f9d,
            0xb3af_8328_5c2d_f711,
            0x6da4_d435_f3b6_17cd,
            0x1d9b_efcd_05a5_323e,
        ],
        [
            0xe673_b13a_075a_65ec,
            0xdb36_395d_f7be_3b99,
            0xcbb1_ac09_1875_24c7,
            0x275d_c4a2_88d1_afb3,
        ],
    ],
};

pub const DELTA_NEG: G2Point = G2Point {
    x: [
        [
            0xbfde_62e2_9179_8139,
            0xa368_bd04_ab35_d024,
            0x957b_d593_8e8f_1152,
            0x0db4_1636_ef18_ba8e,
        ],
        [
            0xfd57_503d_2717_e5cb,
            0xdaa9_bd4e_7142_b3b1,
            0x4a01_4a84_1573_6b73,
            0x2868_06b2_7be1_b951,
        ],
    ],
    y: [
        [
            0xb93d_8367_0841_38f9,
            0x4915_a3f3_7bc1_0821,
            0x5148_c40d_2de5_bce2,
            0x167a_d56e_f8d9_0621,
        ],
        [
            0xc26e_2d0c_7f6a_d458,
            0xfb1f_fc8d_bde0_4983,
            0x18f0_ae0b_1848_8cee,
            0x0220_1b9f_d32c_a208,
        ],
    ],
};

/// `L`'s bases: the constant term, then one per public input.
pub const IC: [G1Point; N_INPUTS + 1] = [
    G1Point {
        x: [
            0x83c3_6583_d153_34d2,
            0x12ae_d501_1ad2_516c,
            0xdbf2_cdde_510e_3533,
            0x1c17_fe8f_9131_6811,
        ],
        y: [
            0x3fb1_e126_f31d_9a1e,
            0xde82_3095_095c_9d1c,
            0x3f06_ddab_1a7e_82cc,
            0x1a80_ff1d_7d53_308e,
        ],
    },
    G1Point {
        x: [
            0xfe6a_887f_4132_e1ef,
            0x03b0_2b71_c406_bce2,
            0x1cd4_9664_b955_6209,
            0x2815_b4ef_d711_737e,
        ],
        y: [
            0xa1eb_3bf4_40a1_5c0b,
            0x68c5_f525_1028_13db,
            0x7cd4_36c1_0d4e_2fa9,
            0x1823_4e6f_87d2_56ca,
        ],
    },
    G1Point {
        x: [
            0x33e0_19fd_d9d3_1913,
            0x457c_6b82_9749_91ae,
            0xb24d_af01_f515_196b,
            0x17b9_e8b3_de09_564b,
        ],
        y: [
            0x1c48_1e52_6ac9_ed98,
            0xe4f1_d56b_8479_6636,
            0x0d80_494d_f5c0_fae7,
            0x0157_0ecb_5be6_0d3c,
        ],
    },
    G1Point {
        x: [
            0x17d5_d7a4_37c3_e33f,
            0xce15_824c_8933_796f,
            0x620c_0d28_10a7_73f2,
            0x1172_5b0e_546c_ef60,
        ],
        y: [
            0x3334_2c52_cf56_fccc,
            0x1e5c_ae24_4db0_94d0,
            0xae8d_8c40_9e32_ecc3,
            0x0931_0cb1_b82d_a76b,
        ],
    },
    G1Point {
        x: [
            0x67af_b532_6788_2598,
            0x2eac_1f70_9be0_9a79,
            0xe583_eacc_2b35_48c3,
            0x0775_9aa2_d964_ab97,
        ],
        y: [
            0x576d_a1cc_275a_4e5c,
            0x6091_0f09_3c44_5981,
            0x28f9_cbc6_ce24_ab29,
            0x1ca8_42db_37e6_7787,
        ],
    },
    G1Point {
        x: [
            0x9d21_7750_3b1b_3223,
            0x9548_4746_6ac5_6d71,
            0xca4b_a650_85ae_7e01,
            0x04dd_4edf_45d2_de7c,
        ],
        y: [
            0x80bc_15a1_740f_e61e,
            0x4d04_0380_1d45_fa55,
            0x4afc_5480_1e25_a8b1,
            0x12bd_4fe6_8947_c98a,
        ],
    },
    G1Point {
        x: [
            0xd6c1_216c_ec85_c389,
            0xedfc_daed_db1d_0a15,
            0x4256_b537_8957_327a,
            0x013a_98c8_e88b_fcf3,
        ],
        y: [
            0x5976_2e2e_994a_bbb4,
            0x1f6f_89e5_0101_dd33,
            0x3e93_0c44_6993_6f28,
            0x0533_ec0b_4bf6_39bd,
        ],
    },
    G1Point {
        x: [
            0xed61_2aa3_c8f6_be8e,
            0x6409_4eba_828c_af3b,
            0xb501_448d_99f6_51a0,
            0x1737_eb74_5d96_6721,
        ],
        y: [
            0xb444_68c3_1d49_ddaa,
            0xd8f3_3231_319b_5310,
            0x24fb_fd42_a44d_97cf,
            0x27e5_1a03_ddb1_d6b7,
        ],
    },
    G1Point {
        x: [
            0xb657_f0a1_72c1_459e,
            0x37d2_7d08_9e7d_5942,
            0x77d6_76d7_7329_a59e,
            0x042c_d3e1_1478_6929,
        ],
        y: [
            0x3405_d1e3_b643_ab16,
            0x475b_9ed7_47a6_9783,
            0x73dc_b83c_62c4_c010,
            0x00e6_5a19_0090_da3f,
        ],
    },
    G1Point {
        x: [
            0x958a_b96b_2cdb_eb8f,
            0x9d07_6d55_7171_af48,
            0x62cb_c455_c8ce_32d4,
            0x2656_6b0e_bf68_9f6f,
        ],
        y: [
            0x1e43_9447_93da_3b47,
            0x5b55_8ed2_f7c5_9f86,
            0x757a_75e2_29e1_767f,
            0x26b4_33e7_6637_a8db,
        ],
    },
    G1Point {
        x: [
            0x7986_4ee6_15f1_1dd4,
            0xa9b3_f28e_559b_469a,
            0x6940_1055_302b_07db,
            0x16c2_b2e1_250b_620d,
        ],
        y: [
            0xfee6_2e6b_de26_eec8,
            0x343e_85cb_d1f3_5253,
            0x5f73_3568_7fb4_54d2,
            0x0131_f8ce_6754_6df5,
        ],
    },
    G1Point {
        x: [
            0xe84f_dfe7_fc76_2d40,
            0x1275_c57c_4376_db9d,
            0xa5e4_539f_1a6b_1e4c,
            0x1f2b_0607_b98e_236b,
        ],
        y: [
            0xd579_6ef9_1dc5_d2f2,
            0x1031_4332_a552_b5f4,
            0x2541_28a8_48cf_a961,
            0x1fa5_8e44_2eab_0488,
        ],
    },
    G1Point {
        x: [
            0x9e01_cdff_98f7_7faa,
            0x03c6_4a5a_41a4_2b8f,
            0x61f5_47ee_accd_7799,
            0x1ea5_7f67_4c45_2802,
        ],
        y: [
            0x23b7_442f_3273_2417,
            0x9cb0_1cce_079a_70a2,
            0x5727_2511_dee0_a4a3,
            0x1826_9685_2b44_dcbb,
        ],
    },
    G1Point {
        x: [
            0x61c8_1a38_17a4_f19b,
            0x14e8_30a6_4d52_11e3,
            0xb4ef_5754_37e8_d06b,
            0x1875_b6f1_eee3_2f39,
        ],
        y: [
            0xbd19_7ddd_ea5c_67d7,
            0xcdb9_068e_a7fb_c8e8,
            0x13e1_7508_65cc_a9ca,
            0x0263_6a0e_50c3_a033,
        ],
    },
    G1Point {
        x: [
            0xa10d_1411_4259_f4db,
            0xf745_c1bf_a8c2_a024,
            0xaaec_7303_9221_00c2,
            0x125c_848f_6dc8_2862,
        ],
        y: [
            0x569e_8998_54c5_d6e5,
            0x71df_d3cf_dc80_db08,
            0x37b2_62d2_506d_7c2c,
            0x08f5_4a56_a231_3cd5,
        ],
    },
    G1Point {
        x: [
            0x7509_ef10_593e_7f10,
            0xf710_115d_52ec_c0bf,
            0x4f5f_08ec_6e4a_16e8,
            0x2146_02b5_e44d_28e0,
        ],
        y: [
            0x0aa0_528a_8b53_75b7,
            0xb393_dac5_e263_095b,
            0x25bd_1721_c220_c4b1,
            0x1aff_5f62_e217_e74e,
        ],
    },
];

/// The bits of an input `L`'s sum takes at once.
const WINDOW: usize = 8;

/// `[k] IC[i + 1]` for `k` in `1..2^WINDOW`: what a window of input `i` adds.
///
/// One constant per input, so that no one evaluation runs long.
macro_rules! windows {
    ($($i:literal),*) => {
        static WINDOWS: [[G1Affine; (1 << WINDOW) - 1]; N_INPUTS] = [$({
            const MULTIPLES: [G1Affine; (1 << WINDOW) - 1] = G1Jacobian::multiples(&G1Affine::constant(&IC[$i + 1]));
            MULTIPLES
        }),*];
    };
}
windows!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);

/// `IC[0]`.
const IC_0: G1Affine = G1Affine::constant(&IC[0]);

/// The lines of `-gamma` and `-delta`, normalized.
pub(crate) static GAMMA_NEG_LINES: [NormalizedLine; N_LINES] = normalize(&prepare(&G2Affine::constant(&GAMMA_NEG)));
pub(crate) static DELTA_NEG_LINES: [NormalizedLine; N_LINES] = normalize(&prepare(&G2Affine::constant(&DELTA_NEG)));

/// The Miller loop of `(alpha, -beta)`, which the proof does not change.
pub(crate) const ALPHA_BETA_NEG: Fp12 =
    miller_loop_prepared(&G1Affine::constant(&ALPHA), &prepare(&G2Affine::constant(&BETA_NEG)));

/// `r`, the order of the groups, little-endian limbs: a public input is below it.
const R: [u64; 4] = [
    0x43e1_f593_f000_0001,
    0x2833_e848_79b9_7091,
    0xb850_45b6_8181_585d,
    0x3064_4e72_e131_a029,
];

/// `L`, or `None` at infinity; an input not below `r` is refused.
///
/// The sum shares its doublings: from the top window down, `WINDOW` doublings, then for each
/// input the multiple of its base its window says.
pub(crate) fn public_input_point(inputs: &[[u64; 4]; N_INPUTS]) -> Result<Option<G1Affine>, Error> {
    if !inputs.iter().all(below_r) {
        return Err(Error::InputNotInField);
    }
    let mut acc = G1Jacobian::INFINITY;
    for window in (0..256 / WINDOW).rev() {
        if !acc.is_infinity() {
            for _ in 0..WINDOW {
                acc = acc.double();
            }
        }
        let (limb, shift) = (window * WINDOW / 64, window * WINDOW % 64);
        for (x, multiples) in inputs.iter().zip(&WINDOWS) {
            let digit = (x[limb] >> shift) as usize & ((1 << WINDOW) - 1);
            if digit != 0 {
                acc = acc.add_affine(&multiples[digit - 1]);
            }
        }
    }
    Ok(acc.add_affine(&IC_0).to_affine())
}

/// Whether `x < r`, comparing from the top limb.
fn below_r(x: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if x[i] != R[i] {
            return x[i] < R[i];
        }
    }
    false
}
