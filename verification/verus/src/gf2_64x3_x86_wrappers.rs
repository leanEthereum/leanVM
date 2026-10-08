//! Copies of the public lane-major wrappers in `gf2_64x3.rs`, using the configured x86 kernels.
use super::x86_64::*;
use super::*;
use core::mem::MaybeUninit;
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::MemContents;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::maybe_uninit::MaybeUninitAdditionalSpecFns;

verus! {
#[derive(Clone,Copy)]
pub struct MixedSums8 { acc: MixedAcc8 }
impl MixedSums8 {
    pub closed spec fn value(self,i: int) -> F192 { e_value(acc8_row(self.acc,i)) }
    pub const fn new() -> (r: Self)
        ensures forall|i: int| 0 <= i < 8 ==> #[trigger] r.value(i) == F192::ZERO,
    {
        proof { lemma_zeroed_acc8(); lemma_u_zero(); }
        Self { acc: unsafe { core::mem::zeroed() } }
    }
    pub fn add(&mut self,t: F192,k: [F64;8])
        ensures forall|i: int| 0 <= i < 8 ==> #[trigger] final(self).value(i) == e_add(old(self).value(i),e_mul(t,e_from_k(k[i].0))),
    {
        let ghost old_acc = self.acc;
        unsafe { mul_base8_add(&mut self.acc,t,k); }
        proof {
            assert forall|i: int| 0 <= i < 8 implies #[trigger] self.value(i) == e_add(e_value(acc8_row(old_acc,i)),e_mul(t,e_from_k(k[i].0))) by {
                lemma_base_unreduced(t,k[i].0);
                lemma_e_value_xor(acc8_row(old_acc,i),base_unreduced(t,k[i].0));
            }
        }
    }
    pub fn reduce(self) -> (r: [F192;8])
        ensures forall|i: int| 0 <= i < 8 ==> #[trigger] r[i] == self.value(i),
    { unsafe { mul_base8_reduce(self.acc) } }
}
impl Default for MixedSums8 {
    fn default() -> (r: Self)
        ensures forall|i: int| 0 <= i < 8 ==> #[trigger] r.value(i) == F192::ZERO,
    { Self::new() }
}

#[derive(Clone,Copy)]
pub struct F192x4 { lanes: Lanes4 }
#[derive(Clone,Copy)]
pub struct F192x4Unreduced { lanes: Wide4 }
impl F192x4 {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool { lanes4_ok(self.lanes) }
    pub closed spec fn elem(self,i: int) -> F192 { lanes4_elem(self.lanes,i) }
    pub fn new(v: [F192;4]) -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.elem(i) == v[i],
    { Self { lanes: unsafe { lanes4(v) } } }
    pub fn splat(v: F192) -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.elem(i) == v,
    { Self::new([v;4]) }
    pub fn load(v: &[F192;4]) -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.elem(i) == v[i],
    { Self { lanes: unsafe { load_lanes4(v) } } }
    pub fn store(self,out: &mut [MaybeUninit<F192>;4])
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] final(out)[i].mem_contents() == MemContents::Init(self.elem(i)),
    {
        proof { use_type_invariant(&self); }
        unsafe { store_lanes4(self.lanes,out); }
    }
    pub fn to_array(self) -> (r: [F192;4])
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r[i] == self.elem(i),
    {
        let mut out = [MaybeUninit::uninit();4];
        self.store(&mut out);
        unsafe { [out[0].assume_init(),out[1].assume_init(),out[2].assume_init(),out[3].assume_init()] }
    }
    pub fn transpose(rows: [Self;4]) -> (r: [Self;4])
        ensures forall|i: int,j: int| 0 <= i < 4 && 0 <= j < 4 ==> #[trigger] r[i].elem(j) == rows[j].elem(i),
    {
        let (a,b,c,d) = (rows[0],rows[1],rows[2],rows[3]);
        proof {
            use_type_invariant(&a); use_type_invariant(&b);
            use_type_invariant(&c); use_type_invariant(&d);
        }
        let lanes = unsafe { transpose_lanes4([rows[0].lanes,rows[1].lanes,rows[2].lanes,rows[3].lanes]) };
        [Self { lanes:lanes[0] },Self { lanes:lanes[1] },Self { lanes:lanes[2] },Self { lanes:lanes[3] }]
    }
    pub fn mul_unreduced(self,rhs: Self) -> (r: F192x4Unreduced)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.value(i) == e_mul(self.elem(i),rhs.elem(i)),
    {
        proof { use_type_invariant(&self); use_type_invariant(&rhs); }
        let r = F192x4Unreduced { lanes: unsafe { mul_lanes4(self.lanes,rhs.lanes) } };
        proof {
            assert forall|i: int| 0 <= i < 4 implies #[trigger] r.value(i) == e_mul(self.elem(i),rhs.elem(i)) by {
                lemma_prod_unreduced(self.elem(i),rhs.elem(i));
            }
        }
        r
    }
}
impl Add for F192x4 {
    type Output = Self;
    fn add(self,rhs: Self) -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.elem(i) == e_add(self.elem(i),rhs.elem(i)),
    {
        proof { use_type_invariant(&self); use_type_invariant(&rhs); }
        let lanes = unsafe { xor_lanes(self.lanes,rhs.lanes) };
        proof { lemma_lanes4_xor(self.lanes,rhs.lanes,lanes); }
        Self { lanes }
    }
}
impl Mul for F192x4 {
    type Output = Self;
    fn mul(self,rhs: Self) -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.elem(i) == e_mul(self.elem(i),rhs.elem(i)),
    {
        // The production nested kernel calls, factored through the two verified wrappers.
        self.mul_unreduced(rhs).reduce()
    }
}
impl F192x4Unreduced {
    pub closed spec fn value(self,i: int) -> F192 { e_value(wide4_value(self.lanes,i)) }
    pub const fn zero() -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.value(i) == F192::ZERO,
    {
        proof { lemma_zeroed_wide4(); lemma_u_zero(); }
        Self { lanes: unsafe { core::mem::zeroed() } }
    }
    pub fn sum(self) -> (r: F192Unreduced)
        ensures e_value(r) == e_add(e_add(e_add(self.value(0),self.value(1)),self.value(2)),self.value(3)),
    { unsafe { sum_lanes4(self.lanes) } }
    pub fn reduce(self) -> (r: F192x4)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.elem(i) == self.value(i),
    { F192x4 { lanes: unsafe { reduce_lanes4(self.lanes) } } }
}
impl BitXorAssign for F192x4Unreduced {
    fn bitxor_assign(&mut self,rhs: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] final(self).value(i) == e_add(old(self).value(i),rhs.value(i)),
    {
        let ghost before = self.lanes;
        self.lanes = unsafe { xor_lanes(self.lanes,rhs.lanes) };
        proof {
            lemma_wide4_xor(before,rhs.lanes,self.lanes);
            assert forall|i: int| 0 <= i < 4 implies #[trigger] self.value(i) == e_add(e_value(wide4_value(before,i)),rhs.value(i)) by {
                lemma_e_value_xor(wide4_value(before,i),wide4_value(rhs.lanes,i));
            }
        }
    }
}
impl BitXor for F192x4Unreduced {
    type Output = Self;
    fn bitxor(self,rhs: Self) -> (r: Self)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] r.value(i) == e_add(self.value(i),rhs.value(i)),
    { let mut s = self; s ^= rhs; s }
}
// Registers have no canonical bit-level representation in the trait spec. The concrete
// operator contracts above specify lane values, as for F192x1.
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl for F192x4 {
    open spec fn obeys_add_spec() -> bool { false }
    open spec fn add_req(self,rhs: Self) -> bool { true }
    open spec fn add_spec(self,rhs: Self) -> Self { self }
}
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl for F192x4 {
    open spec fn obeys_mul_spec() -> bool { false }
    open spec fn mul_req(self,rhs: Self) -> bool { true }
    open spec fn mul_spec(self,rhs: Self) -> Self { self }
}
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorSpecImpl for F192x4Unreduced {
    open spec fn obeys_bitxor_spec() -> bool { false }
    open spec fn bitxor_req(self,rhs: Self) -> bool { true }
    open spec fn bitxor_spec(self,rhs: Self) -> Self { self }
}
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::BitXorAssignSpecImpl for F192x4Unreduced {
    open spec fn obeys_bitxor_assign_spec() -> bool { false }
    open spec fn bitxor_assign_req(&self,rhs: Self) -> bool { true }
    open spec fn bitxor_assign_spec(&self,rhs: Self) -> &Self { self }
}
} // verus!
