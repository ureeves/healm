use crate::Aggregate;

use blake3::{Hash, Hasher};

unsafe impl Aggregate for Hash {
    fn aggregate(nodes: &[Self]) -> Self {
        let mut hasher = Hasher::new();
        for node in nodes {
            hasher.update(node.as_bytes());
        }
        hasher.finalize()
    }
}

#[cfg(all(test, feature = "bench"))]
mod benches {
    use super::*;

    extern crate test;
    use test::Bencher;

    use paste::paste;
    use rand::{rngs::StdRng, RngCore, SeedableRng};

    use crate::HamTree;

    // A macro that generates bench cases for the given arity and height.
    macro_rules! bench_tests {
        (H=$height:literal; A = $($arity:literal),+) => {
            $(
            paste! {
                mod [<tree _ h $height _ a $arity>] {
                    use super::*;

                    #[bench]
                    fn insert(b: &mut Bencher) {
                        type Tree = HamTree<Hash, $height, $arity>;

                        let mut rng = StdRng::seed_from_u64(0xBAAD_F00D);
                        let mut tree = Tree::new();

                        let hash = Hash::from_bytes([42; 32]);

                        b.iter(|| {
                            let i = (rng.next_u64() % Tree::N_LEAVES as u64) as usize;
                            tree.insert(i, hash);
                        });
                    }
                }
            }
            )+
        };
    }

    bench_tests!(H = 0; A = 2, 3, 4, 5);
    bench_tests!(H = 1; A = 2, 3, 4, 5);
    bench_tests!(H = 2; A = 2, 3, 4, 5);
    bench_tests!(H = 3; A = 2, 3, 4, 5);
    bench_tests!(H = 4; A = 2, 3, 4, 5);
    bench_tests!(H = 5; A = 2, 3, 4, 5);
    bench_tests!(H = 6; A = 2, 3, 4, 5);
    bench_tests!(H = 7; A = 2, 3, 4, 5);
    bench_tests!(H = 8; A = 2, 3, 4, 5);
}
