pub trait CopyParents {
    type Left: Copy;
    type Right: Copy;

    fn copy_pair(&self, left: &Self::Left, right: &Self::Right) -> (Self::Left, Self::Right) {
        (*left, *right)
    }
}
